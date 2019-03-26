const std = @import("std");
const builtin = @import("builtin");
const debug = std.debug;
const testing = std.testing;
const math = std.math;
const mem = std.mem;
const Allocator = mem.Allocator;
const ArrayList = std.ArrayList;
const maxInt = std.math.maxInt;
const minInt = std.math.minInt;

const TypeId = builtin.TypeId;

pub const Limb = usize;
pub const DoubleLimb = @IntType(false, 2 * Limb.bit_count);
pub const Log2Limb = math.Log2Int(Limb);

comptime {
    debug.assert(math.floorPowerOfTwo(usize, Limb.bit_count) == Limb.bit_count);
    debug.assert(Limb.bit_count <= 64); // u128 set is unsupported
    debug.assert(Limb.is_signed == false);
}

pub const Int = struct {
    allocator: ?*Allocator,
    positive: bool,
    //  - little-endian ordered
    //  - len >= 1 always
    //  - zero value -> len == 1 with limbs[0] == 0
    limbs: []Limb,
    len: usize,

    const default_capacity = 4;

    pub fn init(allocator: *Allocator) !Int {
        return try Int.initCapacity(allocator, default_capacity);
    }

    pub fn initSet(allocator: *Allocator, value: var) !Int {
        var s = try Int.init(allocator);
        try s.set(value);
        return s;
    }

    pub fn initCapacity(allocator: *Allocator, capacity: usize) !Int {
        return Int{
            .allocator = allocator,
            .positive = true,
            .limbs = block: {
                var limbs = try allocator.alloc(Limb, math.max(default_capacity, capacity));
                limbs[0] = 0;
                break :block limbs;
            },
            .len = 1,
        };
    }

    // Initialize an Int directly from a fixed set of limb values. This is considered read-only
    // and cannot be used as a receiver argument to any functions. If this tries to allocate
    // at any point a panic will occur due to the null allocator.
    pub fn initFixed(limbs: []const Limb) Int {
        var self = Int{
            .allocator = null,
            .positive = true,
            // Cast away the const, invalid use to pass as a pointer argument.
            .limbs = @intToPtr([*]Limb, @ptrToInt(limbs.ptr))[0..limbs.len],
            .len = limbs.len,
        };

        self.normN(limbs.len);
        return self;
    }

    pub fn ensureCapacity(self: *Int, capacity: usize) !void {
        self.assertWritable();
        if (capacity <= self.limbs.len) {
            return;
        }

        self.limbs = try self.allocator.?.realloc(self.limbs, capacity);
    }

    fn assertWritable(self: Int) void {
        if (self.allocator == null) {
            @panic("provided Int value is read-only but must be writable");
        }
    }

    pub fn deinit(self: *Int) void {
        self.assertWritable();
        self.allocator.?.free(self.limbs);
        self.* = undefined;
    }

    pub fn clone(other: Int) !Int {
        return Int{
            .allocator = other.allocator,
            .positive = other.positive,
            .limbs = block: {
                var limbs = try other.allocator.?.alloc(Limb, other.len);
                mem.copy(Limb, limbs[0..], other.limbs[0..other.len]);
                break :block limbs;
            },
            .len = other.len,
        };
    }

    pub fn copy(self: *Int, other: Int) !void {
        self.assertWritable();
        if (self.limbs.ptr == other.limbs.ptr) {
            return;
        }

        self.positive = other.positive;
        try self.ensureCapacity(other.len);
        mem.copy(Limb, self.limbs[0..], other.limbs[0..other.len]);
        self.len = other.len;
    }

    pub fn swap(self: *Int, other: *Int) void {
        self.assertWritable();
        mem.swap(Int, self, other);
    }

    pub fn dump(self: Int) void {
        for (self.limbs) |limb| {
            debug.warn("{x} ", limb);
        }
        debug.warn("\n");
    }

    pub fn negate(self: *Int) void {
        self.positive = !self.positive;
    }

    pub fn abs(self: *Int) void {
        self.positive = true;
    }

    pub fn isOdd(self: Int) bool {
        return self.limbs[0] & 1 != 0;
    }

    pub fn isEven(self: Int) bool {
        return !self.isOdd();
    }

    // Returns the number of bits required to represent the absolute value of self.
    fn bitCountAbs(self: Int) usize {
        return (self.len - 1) * Limb.bit_count + (Limb.bit_count - @clz(self.limbs[self.len - 1]));
    }

    // Returns the number of bits required to represent the integer in twos-complement form.
    //
    // If the integer is negative the value returned is the number of bits needed by a signed
    // integer to represent the value. If positive the value is the number of bits for an
    // unsigned integer. Any unsigned integer will fit in the signed integer with bitcount
    // one greater than the returned value.
    //
    // e.g. -127 returns 8 as it will fit in an i8. 127 returns 7 since it fits in a u7.
    fn bitCountTwosComp(self: Int) usize {
        var bits = self.bitCountAbs();

        // If the entire value has only one bit set (e.g. 0b100000000) then the negation in twos
        // complement requires one less bit.
        if (!self.positive) block: {
            bits += 1;

            if (@popCount(self.limbs[self.len - 1]) == 1) {
                for (self.limbs[0 .. self.len - 1]) |limb| {
                    if (@popCount(limb) != 0) {
                        break :block;
                    }
                }

                bits -= 1;
            }
        }

        return bits;
    }

    pub fn fitsInTwosComp(self: Int, is_signed: bool, bit_count: usize) bool {
        if (self.eqZero()) {
            return true;
        }
        if (!is_signed and !self.positive) {
            return false;
        }

        const req_bits = self.bitCountTwosComp() + @boolToInt(self.positive and is_signed);
        return bit_count >= req_bits;
    }

    pub fn fits(self: Int, comptime T: type) bool {
        return self.fitsInTwosComp(T.is_signed, T.bit_count);
    }

    // Returns the approximate size of the integer in the given base. Negative values accommodate for
    // the minus sign. This is used for determining the number of characters needed to print the
    // value. It is inexact and will exceed the given value by 1-2 digits.
    pub fn sizeInBase(self: Int, base: usize) usize {
        const bit_count = usize(@boolToInt(!self.positive)) + self.bitCountAbs();
        return (bit_count / math.log2(base)) + 1;
    }

    pub fn set(self: *Int, value: var) Allocator.Error!void {
        self.assertWritable();
        const T = @typeOf(value);

        switch (@typeInfo(T)) {
            TypeId.Int => |info| {
                const UT = if (T.is_signed) @IntType(false, T.bit_count - 1) else T;

                try self.ensureCapacity(@sizeOf(UT) / @sizeOf(Limb));
                self.positive = value >= 0;
                self.len = 0;

                var w_value: UT = if (value < 0) @intCast(UT, -value) else @intCast(UT, value);

                if (info.bits <= Limb.bit_count) {
                    self.limbs[0] = Limb(w_value);
                    self.len = 1;
                } else {
                    var i: usize = 0;
                    while (w_value != 0) : (i += 1) {
                        self.limbs[i] = @truncate(Limb, w_value);
                        self.len += 1;

                        // TODO: shift == 64 at compile-time fails. Fails on u128 limbs.
                        w_value >>= Limb.bit_count / 2;
                        w_value >>= Limb.bit_count / 2;
                    }
                }
            },
            TypeId.ComptimeInt => {
                comptime var w_value = if (value < 0) -value else value;

                const req_limbs = @divFloor(math.log2(w_value), Limb.bit_count) + 1;
                try self.ensureCapacity(req_limbs);

                self.positive = value >= 0;
                self.len = req_limbs;

                if (w_value <= maxInt(Limb)) {
                    self.limbs[0] = w_value;
                } else {
                    const mask = (1 << Limb.bit_count) - 1;

                    comptime var i = 0;
                    inline while (w_value != 0) : (i += 1) {
                        self.limbs[i] = w_value & mask;

                        w_value >>= Limb.bit_count / 2;
                        w_value >>= Limb.bit_count / 2;
                    }
                }
            },
            else => {
                @compileError("cannot set Int using type " ++ @typeName(T));
            },
        }
    }

    pub const ConvertError = error{
        NegativeIntoUnsigned,
        TargetTooSmall,
    };

    pub fn to(self: Int, comptime T: type) ConvertError!T {
        switch (@typeId(T)) {
            TypeId.Int => {
                const UT = @IntType(false, T.bit_count);

                if (self.bitCountTwosComp() > T.bit_count) {
                    return error.TargetTooSmall;
                }

                var r: UT = 0;

                if (@sizeOf(UT) <= @sizeOf(Limb)) {
                    r = @intCast(UT, self.limbs[0]);
                } else {
                    for (self.limbs[0..self.len]) |_, ri| {
                        const limb = self.limbs[self.len - ri - 1];
                        r <<= Limb.bit_count;
                        r |= limb;
                    }
                }

                if (!T.is_signed) {
                    return if (self.positive) @intCast(T, r) else error.NegativeIntoUnsigned;
                } else {
                    if (self.positive) {
                        return @intCast(T, r);
                    } else {
                        if (math.cast(T, r)) |ok| {
                            return -ok;
                        } else |_| {
                            return minInt(T);
                        }
                    }
                }
            },
            else => {
                @compileError("cannot convert Int to type " ++ @typeName(T));
            },
        }
    }

    fn charToDigit(ch: u8, base: u8) !u8 {
        const d = switch (ch) {
            '0'...'9' => ch - '0',
            'a'...'f' => (ch - 'a') + 0xa,
            else => return error.InvalidCharForDigit,
        };

        return if (d < base) d else return error.DigitTooLargeForBase;
    }

    fn digitToChar(d: u8, base: u8) !u8 {
        if (d >= base) {
            return error.DigitTooLargeForBase;
        }

        return switch (d) {
            0...9 => '0' + d,
            0xa...0xf => ('a' - 0xa) + d,
            else => unreachable,
        };
    }

    pub fn setString(self: *Int, base: u8, value: []const u8) !void {
        self.assertWritable();
        if (base < 2 or base > 16) {
            return error.InvalidBase;
        }

        var i: usize = 0;
        var positive = true;
        if (value.len > 0 and value[0] == '-') {
            positive = false;
            i += 1;
        }

        const ap_base = Int.initFixed(([]Limb{base})[0..]);
        try self.set(0);

        for (value[i..]) |ch| {
            const d = try charToDigit(ch, base);

            const ap_d = Int.initFixed(([]Limb{d})[0..]);

            try self.mul(self.*, ap_base);
            try self.add(self.*, ap_d);
        }
        self.positive = positive;
    }

    /// TODO make this call format instead of the other way around
    pub fn toString(self: Int, allocator: *Allocator, base: u8) ![]const u8 {
        if (base < 2 or base > 16) {
            return error.InvalidBase;
        }

        var digits = ArrayList(u8).init(allocator);
        try digits.ensureCapacity(self.sizeInBase(base) + 1);
        defer digits.deinit();

        if (self.eqZero()) {
            try digits.append('0');
            return digits.toOwnedSlice();
        }

        // Power of two: can do a single pass and use masks to extract digits.
        if (base & (base - 1) == 0) {
            const base_shift = math.log2_int(Limb, base);

            for (self.limbs[0..self.len]) |limb| {
                var shift: usize = 0;
                while (shift < Limb.bit_count) : (shift += base_shift) {
                    const r = @intCast(u8, (limb >> @intCast(Log2Limb, shift)) & Limb(base - 1));
                    const ch = try digitToChar(r, base);
                    try digits.append(ch);
                }
            }

            while (true) {
                // always will have a non-zero digit somewhere
                const c = digits.pop();
                if (c != '0') {
                    digits.append(c) catch unreachable;
                    break;
                }
            }
        } // Non power-of-two: batch divisions per word size.
        else {
            const digits_per_limb = math.log(Limb, base, maxInt(Limb));
            var limb_base: Limb = 1;
            var j: usize = 0;
            while (j < digits_per_limb) : (j += 1) {
                limb_base *= base;
            }

            var q = try self.clone();
            q.positive = true;
            var r = try Int.init(allocator);
            var b = try Int.initSet(allocator, limb_base);

            while (q.len >= 2) {
                try Int.divTrunc(&q, &r, q, b);

                var r_word = r.limbs[0];
                var i: usize = 0;
                while (i < digits_per_limb) : (i += 1) {
                    const ch = try digitToChar(@intCast(u8, r_word % base), base);
                    r_word /= base;
                    try digits.append(ch);
                }
            }

            {
                debug.assert(q.len == 1);

                var r_word = q.limbs[0];
                while (r_word != 0) {
                    const ch = try digitToChar(@intCast(u8, r_word % base), base);
                    r_word /= base;
                    try digits.append(ch);
                }
            }
        }

        if (!self.positive) {
            try digits.append('-');
        }

        var s = digits.toOwnedSlice();
        mem.reverse(u8, s);
        return s;
    }

    /// for the std lib format function
    /// TODO make this non-allocating
    pub fn format(
        self: Int,
        comptime fmt: []const u8,
        context: var,
        comptime FmtError: type,
        output: fn (@typeOf(context), []const u8) FmtError!void,
    ) FmtError!void {
        // TODO look at fmt and support other bases
        const str = self.toString(self.allocator, 10) catch @panic("TODO make this non allocating");
        defer self.allocator.free(str);
        return output(context, str);
    }

    // returns -1, 0, 1 if |a| < |b|, |a| == |b| or |a| > |b| respectively.
    pub fn cmpAbs(a: Int, b: Int) i8 {
        if (a.len < b.len) {
            return -1;
        }
        if (a.len > b.len) {
            return 1;
        }

        var i: usize = a.len - 1;
        while (i != 0) : (i -= 1) {
            if (a.limbs[i] != b.limbs[i]) {
                break;
            }
        }

        if (a.limbs[i] < b.limbs[i]) {
            return -1;
        } else if (a.limbs[i] > b.limbs[i]) {
            return 1;
        } else {
            return 0;
        }
    }

    // returns -1, 0, 1 if a < b, a == b or a > b respectively.
    pub fn cmp(a: Int, b: Int) i8 {
        if (a.positive != b.positive) {
            return if (a.positive) i8(1) else -1;
        } else {
            const r = cmpAbs(a, b);
            return if (a.positive) r else -r;
        }
    }

    // if a == 0
    pub fn eqZero(a: Int) bool {
        return a.len == 1 and a.limbs[0] == 0;
    }

    // if |a| == |b|
    pub fn eqAbs(a: Int, b: Int) bool {
        return cmpAbs(a, b) == 0;
    }

    // if a == b
    pub fn eq(a: Int, b: Int) bool {
        return cmp(a, b) == 0;
    }

    // Normalize for a possible single carry digit.
    //
    // [1, 2, 3, 4, 0] -> [1, 2, 3, 4]
    // [1, 2, 3, 4, 5] -> [1, 2, 3, 4, 5]
    // [0]             -> [0]
    fn norm1(r: *Int, length: usize) void {
        debug.assert(length > 0);
        debug.assert(length <= r.limbs.len);

        if (r.limbs[length - 1] == 0) {
            r.len = if (length > 1) length - 1 else 1;
        } else {
            r.len = length;
        }
    }

    // Normalize a possible sequence of leading zeros.
    //
    // [1, 2, 3, 4, 0] -> [1, 2, 3, 4]
    // [1, 2, 0, 0, 0] -> [1, 2]
    // [0, 0, 0, 0, 0] -> [0]
    fn normN(r: *Int, length: usize) void {
        debug.assert(length > 0);
        debug.assert(length <= r.limbs.len);

        var j = length;
        while (j > 0) : (j -= 1) {
            if (r.limbs[j - 1] != 0) {
                break;
            }
        }

        // Handle zero
        r.len = if (j != 0) j else 1;
    }

    // Cannot be used as a result argument to any function.
    fn readOnlyPositive(a: Int) Int {
        return Int{
            .allocator = null,
            .positive = true,
            .limbs = a.limbs,
            .len = a.len,
        };
    }

    // r = a + b
    pub fn add(r: *Int, a: Int, b: Int) Allocator.Error!void {
        r.assertWritable();
        if (a.eqZero()) {
            try r.copy(b);
            return;
        } else if (b.eqZero()) {
            try r.copy(a);
            return;
        }

        if (a.positive != b.positive) {
            if (a.positive) {
                // (a) + (-b) => a - b
                try r.sub(a, readOnlyPositive(b));
            } else {
                // (-a) + (b) => b - a
                try r.sub(b, readOnlyPositive(a));
            }
        } else {
            if (a.len >= b.len) {
                try r.ensureCapacity(a.len + 1);
                lladd(r.limbs[0..], a.limbs[0..a.len], b.limbs[0..b.len]);
                r.norm1(a.len + 1);
            } else {
                try r.ensureCapacity(b.len + 1);
                lladd(r.limbs[0..], b.limbs[0..b.len], a.limbs[0..a.len]);
                r.norm1(b.len + 1);
            }

            r.positive = a.positive;
        }
    }

    // Knuth 4.3.1, Algorithm A.
    fn lladd(r: []Limb, a: []const Limb, b: []const Limb) void {
        @setRuntimeSafety(false);
        debug.assert(a.len != 0 and b.len != 0);
        debug.assert(a.len >= b.len);
        debug.assert(r.len >= a.len + 1);

        var i: usize = 0;
        var carry: Limb = 0;

        while (i < b.len) : (i += 1) {
            var c: Limb = 0;
            c += @boolToInt(@addWithOverflow(Limb, a[i], b[i], &r[i]));
            c += @boolToInt(@addWithOverflow(Limb, r[i], carry, &r[i]));
            carry = c;
        }

        while (i < a.len) : (i += 1) {
            carry = @boolToInt(@addWithOverflow(Limb, a[i], carry, &r[i]));
        }

        r[i] = carry;
    }

    // r = a - b
    pub fn sub(r: *Int, a: Int, b: Int) !void {
        r.assertWritable();
        if (a.positive != b.positive) {
            if (a.positive) {
                // (a) - (-b) => a + b
                try r.add(a, readOnlyPositive(b));
            } else {
                // (-a) - (b) => -(a + b)
                try r.add(readOnlyPositive(a), b);
                r.positive = false;
            }
        } else {
            if (a.positive) {
                // (a) - (b) => a - b
                if (a.cmp(b) >= 0) {
                    try r.ensureCapacity(a.len + 1);
                    llsub(r.limbs[0..], a.limbs[0..a.len], b.limbs[0..b.len]);
                    r.normN(a.len);
                    r.positive = true;
                } else {
                    try r.ensureCapacity(b.len + 1);
                    llsub(r.limbs[0..], b.limbs[0..b.len], a.limbs[0..a.len]);
                    r.normN(b.len);
                    r.positive = false;
                }
            } else {
                // (-a) - (-b) => -(a - b)
                if (a.cmp(b) < 0) {
                    try r.ensureCapacity(a.len + 1);
                    llsub(r.limbs[0..], a.limbs[0..a.len], b.limbs[0..b.len]);
                    r.normN(a.len);
                    r.positive = false;
                } else {
                    try r.ensureCapacity(b.len + 1);
                    llsub(r.limbs[0..], b.limbs[0..b.len], a.limbs[0..a.len]);
                    r.normN(b.len);
                    r.positive = true;
                }
            }
        }
    }

    // Knuth 4.3.1, Algorithm S.
    fn llsub(r: []Limb, a: []const Limb, b: []const Limb) void {
        @setRuntimeSafety(false);
        debug.assert(a.len != 0 and b.len != 0);
        debug.assert(a.len > b.len or (a.len == b.len and a[a.len - 1] >= b[b.len - 1]));
        debug.assert(r.len >= a.len);

        var i: usize = 0;
        var borrow: Limb = 0;

        while (i < b.len) : (i += 1) {
            var c: Limb = 0;
            c += @boolToInt(@subWithOverflow(Limb, a[i], b[i], &r[i]));
            c += @boolToInt(@subWithOverflow(Limb, r[i], borrow, &r[i]));
            borrow = c;
        }

        while (i < a.len) : (i += 1) {
            borrow = @boolToInt(@subWithOverflow(Limb, a[i], borrow, &r[i]));
        }

        debug.assert(borrow == 0);
    }

    // rma = a * b
    //
    // For greatest efficiency, ensure rma does not alias a or b.
    pub fn mul(rma: *Int, a: Int, b: Int) !void {
        rma.assertWritable();

        var r = rma;
        var aliased = rma.limbs.ptr == a.limbs.ptr or rma.limbs.ptr == b.limbs.ptr;

        var sr: Int = undefined;
        if (aliased) {
            sr = try Int.initCapacity(rma.allocator.?, a.len + b.len);
            r = &sr;
            aliased = true;
        }
        defer if (aliased) {
            rma.swap(r);
            r.deinit();
        };

        try r.ensureCapacity(a.len + b.len);

        if (a.len >= b.len) {
            llmul(r.limbs, a.limbs[0..a.len], b.limbs[0..b.len]);
        } else {
            llmul(r.limbs, b.limbs[0..b.len], a.limbs[0..a.len]);
        }

        r.positive = a.positive == b.positive;
        r.normN(a.len + b.len);
    }

    // a + b * c + *carry, sets carry to the overflow bits
    pub fn addMulLimbWithCarry(a: Limb, b: Limb, c: Limb, carry: *Limb) Limb {
        var r1: Limb = undefined;

        // r1 = a + *carry
        const c1: Limb = @boolToInt(@addWithOverflow(Limb, a, carry.*, &r1));

        // r2 = b * c
        //
        // We still use a DoubleLimb here since the @mulWithOverflow builtin does not
        // return the carry and lower bits separately so we would need to perform this
        // anyway to get the carry bits. The branch on the overflow case costs more than
        // just computing them unconditionally and splitting.
        //
        // This could be a single x86 mul instruction, which stores the carry/lower in rdx:rax.
        const bc = DoubleLimb(b) * DoubleLimb(c);
        const r2 = @truncate(Limb, bc);
        const c2 = @truncate(Limb, bc >> Limb.bit_count);

        // r1 = r1 + r2
        const c3: Limb = @boolToInt(@addWithOverflow(Limb, r1, r2, &r1));

        // This never overflows, c1, c3 are either 0 or 1 and if both are 1 then
        // c2 is at least <= maxInt(Limb) - 2.
        carry.* = c1 + c2 + c3;

        return r1;
    }

    // Knuth 4.3.1, Algorithm M.
    //
    // r MUST NOT alias any of a or b.
    fn llmul(r: []Limb, a: []const Limb, b: []const Limb) void {
        @setRuntimeSafety(false);
        debug.assert(a.len >= b.len);
        debug.assert(r.len >= a.len + b.len);

        mem.set(Limb, r[0 .. a.len + b.len], 0);

        var i: usize = 0;
        while (i < a.len) : (i += 1) {
            var carry: Limb = 0;
            var j: usize = 0;
            while (j < b.len) : (j += 1) {
                r[i + j] = @inlineCall(addMulLimbWithCarry, r[i + j], a[i], b[j], &carry);
            }
            r[i + j] = carry;
        }
    }

    pub fn divFloor(q: *Int, r: *Int, a: Int, b: Int) !void {
        try div(q, r, a, b);

        // Trunc -> Floor.
        if (!q.positive) {
            const one = Int.initFixed(([]Limb{1})[0..]);
            try q.sub(q.*, one);
            try r.add(q.*, one);
        }
        r.positive = b.positive;
    }

    pub fn divTrunc(q: *Int, r: *Int, a: Int, b: Int) !void {
        try div(q, r, a, b);
        r.positive = a.positive;
    }

    // Truncates by default.
    fn div(quo: *Int, rem: *Int, a: Int, b: Int) !void {
        quo.assertWritable();
        rem.assertWritable();

        if (b.eqZero()) {
            @panic("division by zero");
        }
        if (quo == rem) {
            @panic("quo and rem cannot be same variable");
        }

        if (a.cmpAbs(b) < 0) {
            // quo may alias a so handle rem first
            try rem.copy(a);
            rem.positive = a.positive == b.positive;

            quo.positive = true;
            quo.len = 1;
            quo.limbs[0] = 0;
            return;
        }

        if (b.len == 1) {
            try quo.ensureCapacity(a.len);

            lldiv1(quo.limbs[0..], &rem.limbs[0], a.limbs[0..a.len], b.limbs[0]);
            quo.norm1(a.len);
            quo.positive = a.positive == b.positive;

            rem.len = 1;
            rem.positive = true;
        } else {
            // x and y are modified during division
            var x = try a.clone();
            defer x.deinit();

            var y = try b.clone();
            defer y.deinit();

            // x may grow one limb during normalization
            try quo.ensureCapacity(a.len + y.len);
            try divN(quo.allocator.?, quo, rem, &x, &y);

            quo.positive = a.positive == b.positive;
        }
    }

    // Knuth 4.3.1, Exercise 16.
    fn lldiv1(quo: []Limb, rem: *Limb, a: []const Limb, b: Limb) void {
        @setRuntimeSafety(false);
        debug.assert(a.len > 1 or a[0] >= b);
        debug.assert(quo.len >= a.len);

        rem.* = 0;
        for (a) |_, ri| {
            const i = a.len - ri - 1;
            const pdiv = ((DoubleLimb(rem.*) << Limb.bit_count) | a[i]);

            if (pdiv == 0) {
                quo[i] = 0;
                rem.* = 0;
            } else if (pdiv < b) {
                quo[i] = 0;
                rem.* = @truncate(Limb, pdiv);
            } else if (pdiv == b) {
                quo[i] = 1;
                rem.* = 0;
            } else {
                quo[i] = @truncate(Limb, @divTrunc(pdiv, b));
                rem.* = @truncate(Limb, pdiv - (quo[i] *% b));
            }
        }
    }

    // Handbook of Applied Cryptography, 14.20
    //
    // x = qy + r where 0 <= r < y
    fn divN(allocator: *Allocator, q: *Int, r: *Int, x: *Int, y: *Int) !void {
        debug.assert(y.len >= 2);
        debug.assert(x.len >= y.len);
        debug.assert(q.limbs.len >= x.len + y.len - 1);
        debug.assert(default_capacity >= 3); // see 3.2

        var tmp = try Int.init(allocator);
        defer tmp.deinit();

        // Normalize so y > Limb.bit_count / 2 (i.e. leading bit is set)
        const norm_shift = @clz(y.limbs[y.len - 1]);
        try x.shiftLeft(x.*, norm_shift);
        try y.shiftLeft(y.*, norm_shift);

        const n = x.len - 1;
        const t = y.len - 1;

        // 1.
        q.len = n - t + 1;
        mem.set(Limb, q.limbs[0..q.len], 0);

        // 2.
        try tmp.shiftLeft(y.*, Limb.bit_count * (n - t));
        while (x.cmp(tmp) >= 0) {
            q.limbs[n - t] += 1;
            try x.sub(x.*, tmp);
        }

        // 3.
        var i = n;
        while (i > t) : (i -= 1) {
            // 3.1
            if (x.limbs[i] == y.limbs[t]) {
                q.limbs[i - t - 1] = maxInt(Limb);
            } else {
                const num = (DoubleLimb(x.limbs[i]) << Limb.bit_count) | DoubleLimb(x.limbs[i - 1]);
                const z = @intCast(Limb, num / DoubleLimb(y.limbs[t]));
                q.limbs[i - t - 1] = if (z > maxInt(Limb)) maxInt(Limb) else Limb(z);
            }

            // 3.2
            tmp.limbs[0] = if (i >= 2) x.limbs[i - 2] else 0;
            tmp.limbs[1] = if (i >= 1) x.limbs[i - 1] else 0;
            tmp.limbs[2] = x.limbs[i];
            tmp.normN(3);

            while (true) {
                // 2x1 limb multiplication unrolled against single-limb q[i-t-1]
                var carry: Limb = 0;
                r.limbs[0] = addMulLimbWithCarry(0, if (t >= 1) y.limbs[t - 1] else 0, q.limbs[i - t - 1], &carry);
                r.limbs[1] = addMulLimbWithCarry(0, y.limbs[t], q.limbs[i - t - 1], &carry);
                r.limbs[2] = carry;
                r.normN(3);

                if (r.cmpAbs(tmp) <= 0) {
                    break;
                }

                q.limbs[i - t - 1] -= 1;
            }

            // 3.3
            try tmp.set(q.limbs[i - t - 1]);
            try tmp.mul(tmp, y.*);
            try tmp.shiftLeft(tmp, Limb.bit_count * (i - t - 1));
            try x.sub(x.*, tmp);

            if (!x.positive) {
                try tmp.shiftLeft(y.*, Limb.bit_count * (i - t - 1));
                try x.add(x.*, tmp);
                q.limbs[i - t - 1] -= 1;
            }
        }

        // Denormalize
        q.normN(q.len);

        try r.shiftRight(x.*, norm_shift);
        r.normN(r.len);
    }

    // r = a << shift, in other words, r = a * 2^shift
    pub fn shiftLeft(r: *Int, a: Int, shift: usize) !void {
        r.assertWritable();

        try r.ensureCapacity(a.len + (shift / Limb.bit_count) + 1);
        llshl(r.limbs[0..], a.limbs[0..a.len], shift);
        r.norm1(a.len + (shift / Limb.bit_count) + 1);
        r.positive = a.positive;
    }

    fn llshl(r: []Limb, a: []const Limb, shift: usize) void {
        @setRuntimeSafety(false);
        debug.assert(a.len >= 1);
        debug.assert(r.len >= a.len + (shift / Limb.bit_count) + 1);

        const limb_shift = shift / Limb.bit_count + 1;
        const interior_limb_shift = @intCast(Log2Limb, shift % Limb.bit_count);

        var carry: Limb = 0;
        var i: usize = 0;
        while (i < a.len) : (i += 1) {
            const src_i = a.len - i - 1;
            const dst_i = src_i + limb_shift;

            const src_digit = a[src_i];
            r[dst_i] = carry | @inlineCall(math.shr, Limb, src_digit, Limb.bit_count - @intCast(Limb, interior_limb_shift));
            carry = (src_digit << interior_limb_shift);
        }

        r[limb_shift - 1] = carry;
        mem.set(Limb, r[0 .. limb_shift - 1], 0);
    }

    // r = a >> shift
    pub fn shiftRight(r: *Int, a: Int, shift: usize) !void {
        r.assertWritable();

        if (a.len <= shift / Limb.bit_count) {
            r.len = 1;
            r.limbs[0] = 0;
            r.positive = true;
            return;
        }

        try r.ensureCapacity(a.len - (shift / Limb.bit_count));
        const r_len = llshr(r.limbs[0..], a.limbs[0..a.len], shift);
        r.len = a.len - (shift / Limb.bit_count);
        r.positive = a.positive;
    }

    fn llshr(r: []Limb, a: []const Limb, shift: usize) void {
        @setRuntimeSafety(false);
        debug.assert(a.len >= 1);
        debug.assert(r.len >= a.len - (shift / Limb.bit_count));

        const limb_shift = shift / Limb.bit_count;
        const interior_limb_shift = @intCast(Log2Limb, shift % Limb.bit_count);

        var carry: Limb = 0;
        var i: usize = 0;
        while (i < a.len - limb_shift) : (i += 1) {
            const src_i = a.len - i - 1;
            const dst_i = src_i - limb_shift;

            const src_digit = a[src_i];
            r[dst_i] = carry | (src_digit >> interior_limb_shift);
            carry = @inlineCall(math.shl, Limb, src_digit, Limb.bit_count - @intCast(Limb, interior_limb_shift));
        }
    }

    // r = a | b
    pub fn bitOr(r: *Int, a: Int, b: Int) !void {
        r.assertWritable();

        if (a.len > b.len) {
            try r.ensureCapacity(a.len);
            llor(r.limbs[0..], a.limbs[0..a.len], b.limbs[0..b.len]);
            r.len = a.len;
        } else {
            try r.ensureCapacity(b.len);
            llor(r.limbs[0..], b.limbs[0..b.len], a.limbs[0..a.len]);
            r.len = b.len;
        }
    }

    fn llor(r: []Limb, a: []const Limb, b: []const Limb) void {
        @setRuntimeSafety(false);
        debug.assert(r.len >= a.len);
        debug.assert(a.len >= b.len);

        var i: usize = 0;
        while (i < b.len) : (i += 1) {
            r[i] = a[i] | b[i];
        }
        while (i < a.len) : (i += 1) {
            r[i] = a[i];
        }
    }

    // r = a & b
    pub fn bitAnd(r: *Int, a: Int, b: Int) !void {
        r.assertWritable();

        if (a.len > b.len) {
            try r.ensureCapacity(b.len);
            lland(r.limbs[0..], a.limbs[0..a.len], b.limbs[0..b.len]);
            r.normN(b.len);
        } else {
            try r.ensureCapacity(a.len);
            lland(r.limbs[0..], b.limbs[0..b.len], a.limbs[0..a.len]);
            r.normN(a.len);
        }
    }

    fn lland(r: []Limb, a: []const Limb, b: []const Limb) void {
        @setRuntimeSafety(false);
        debug.assert(r.len >= b.len);
        debug.assert(a.len >= b.len);

        var i: usize = 0;
        while (i < b.len) : (i += 1) {
            r[i] = a[i] & b[i];
        }
    }

    // r = a ^ b
    pub fn bitXor(r: *Int, a: Int, b: Int) !void {
        r.assertWritable();

        if (a.len > b.len) {
            try r.ensureCapacity(a.len);
            llxor(r.limbs[0..], a.limbs[0..a.len], b.limbs[0..b.len]);
            r.normN(a.len);
        } else {
            try r.ensureCapacity(b.len);
            llxor(r.limbs[0..], b.limbs[0..b.len], a.limbs[0..a.len]);
            r.normN(b.len);
        }
    }

    fn llxor(r: []Limb, a: []const Limb, b: []const Limb) void {
        @setRuntimeSafety(false);
        debug.assert(r.len >= a.len);
        debug.assert(a.len >= b.len);

        var i: usize = 0;
        while (i < b.len) : (i += 1) {
            r[i] = a[i] ^ b[i];
        }
        while (i < a.len) : (i += 1) {
            r[i] = a[i];
        }
    }
};

// NOTE: All the following tests assume the max machine-word will be 64-bit.
//
// They will still run on larger than this and should pass, but the multi-limb code-paths
// may be untested in some cases.

const al = debug.global_allocator;

test "big.int comptime_int set" {
    comptime var s = 0xefffffff00000001eeeeeeefaaaaaaab;
    var a = try Int.initSet(al, s);

    const s_limb_count = 128 / Limb.bit_count;

    comptime var i: usize = 0;
    inline while (i < s_limb_count) : (i += 1) {
        const result = Limb(s & maxInt(Limb));
        s >>= Limb.bit_count / 2;
        s >>= Limb.bit_count / 2;
        testing.expect(a.limbs[i] == result);
    }
}

test "big.int comptime_int set negative" {
    var a = try Int.initSet(al, -10);

    testing.expect(a.limbs[0] == 10);
    testing.expect(a.positive == false);
}

test "big.int int set unaligned small" {
    var a = try Int.initSet(al, u7(45));

    testing.expect(a.limbs[0] == 45);
    testing.expect(a.positive == true);
}

test "big.int comptime_int to" {
    const a = try Int.initSet(al, 0xefffffff00000001eeeeeeefaaaaaaab);

    testing.expect((try a.to(u128)) == 0xefffffff00000001eeeeeeefaaaaaaab);
}

test "big.int sub-limb to" {
    const a = try Int.initSet(al, 10);

    testing.expect((try a.to(u8)) == 10);
}

test "big.int to target too small error" {
    const a = try Int.initSet(al, 0xffffffff);

    testing.expectError(error.TargetTooSmall, a.to(u8));
}

test "big.int norm1" {
    var a = try Int.init(al);
    try a.ensureCapacity(8);

    a.limbs[0] = 1;
    a.limbs[1] = 2;
    a.limbs[2] = 3;
    a.limbs[3] = 0;
    a.norm1(4);
    testing.expect(a.len == 3);

    a.limbs[0] = 1;
    a.limbs[1] = 2;
    a.limbs[2] = 3;
    a.norm1(3);
    testing.expect(a.len == 3);

    a.limbs[0] = 0;
    a.limbs[1] = 0;
    a.norm1(2);
    testing.expect(a.len == 1);

    a.limbs[0] = 0;
    a.norm1(1);
    testing.expect(a.len == 1);
}

test "big.int normN" {
    var a = try Int.init(al);
    try a.ensureCapacity(8);

    a.limbs[0] = 1;
    a.limbs[1] = 2;
    a.limbs[2] = 0;
    a.limbs[3] = 0;
    a.normN(4);
    testing.expect(a.len == 2);

    a.limbs[0] = 1;
    a.limbs[1] = 2;
    a.limbs[2] = 3;
    a.normN(3);
    testing.expect(a.len == 3);

    a.limbs[0] = 0;
    a.limbs[1] = 0;
    a.limbs[2] = 0;
    a.limbs[3] = 0;
    a.normN(4);
    testing.expect(a.len == 1);

    a.limbs[0] = 0;
    a.normN(1);
    testing.expect(a.len == 1);
}

test "big.int parity" {
    var a = try Int.init(al);
    try a.set(0);
    testing.expect(a.isEven());
    testing.expect(!a.isOdd());

    try a.set(7);
    testing.expect(!a.isEven());
    testing.expect(a.isOdd());
}

test "big.int bitcount + sizeInBase" {
    var a = try Int.init(al);

    try a.set(0b100);
    testing.expect(a.bitCountAbs() == 3);
    testing.expect(a.sizeInBase(2) >= 3);
    testing.expect(a.sizeInBase(10) >= 1);

    a.negate();
    testing.expect(a.bitCountAbs() == 3);
    testing.expect(a.sizeInBase(2) >= 4);
    testing.expect(a.sizeInBase(10) >= 2);

    try a.set(0xffffffff);
    testing.expect(a.bitCountAbs() == 32);
    testing.expect(a.sizeInBase(2) >= 32);
    testing.expect(a.sizeInBase(10) >= 10);

    try a.shiftLeft(a, 5000);
    testing.expect(a.bitCountAbs() == 5032);
    testing.expect(a.sizeInBase(2) >= 5032);
    a.positive = false;

    testing.expect(a.bitCountAbs() == 5032);
    testing.expect(a.sizeInBase(2) >= 5033);
}

test "big.int bitcount/to" {
    var a = try Int.init(al);

    try a.set(0);
    testing.expect(a.bitCountTwosComp() == 0);

    // TODO: stack smashing
    // testing.expect((try a.to(u0)) == 0);
    // TODO: sigsegv
    // testing.expect((try a.to(i0)) == 0);

    try a.set(-1);
    testing.expect(a.bitCountTwosComp() == 1);
    testing.expect((try a.to(i1)) == -1);

    try a.set(-8);
    testing.expect(a.bitCountTwosComp() == 4);
    testing.expect((try a.to(i4)) == -8);

    try a.set(127);
    testing.expect(a.bitCountTwosComp() == 7);
    testing.expect((try a.to(u7)) == 127);

    try a.set(-128);
    testing.expect(a.bitCountTwosComp() == 8);
    testing.expect((try a.to(i8)) == -128);

    try a.set(-129);
    testing.expect(a.bitCountTwosComp() == 9);
    testing.expect((try a.to(i9)) == -129);
}

test "big.int fits" {
    var a = try Int.init(al);

    try a.set(0);
    testing.expect(a.fits(u0));
    testing.expect(a.fits(i0));

    try a.set(255);
    testing.expect(!a.fits(u0));
    testing.expect(!a.fits(u1));
    testing.expect(!a.fits(i8));
    testing.expect(a.fits(u8));
    testing.expect(a.fits(u9));
    testing.expect(a.fits(i9));

    try a.set(-128);
    testing.expect(!a.fits(i7));
    testing.expect(a.fits(i8));
    testing.expect(a.fits(i9));
    testing.expect(!a.fits(u9));

    try a.set(0x1ffffffffeeeeeeee);
    testing.expect(!a.fits(u32));
    testing.expect(!a.fits(u64));
    testing.expect(a.fits(u65));
}

test "big.int string set" {
    var a = try Int.init(al);
    try a.setString(10, "120317241209124781241290847124");

    testing.expect((try a.to(u128)) == 120317241209124781241290847124);
}

test "big.int string negative" {
    var a = try Int.init(al);
    try a.setString(10, "-1023");
    testing.expect((try a.to(i32)) == -1023);
}

test "big.int string set bad char error" {
    var a = try Int.init(al);
    testing.expectError(error.InvalidCharForDigit, a.setString(10, "x"));
}

test "big.int string set bad base error" {
    var a = try Int.init(al);
    testing.expectError(error.InvalidBase, a.setString(45, "10"));
}

test "big.int string to" {
    const a = try Int.initSet(al, 120317241209124781241290847124);

    const as = try a.toString(al, 10);
    const es = "120317241209124781241290847124";

    testing.expect(mem.eql(u8, as, es));
}

test "big.int string to base base error" {
    const a = try Int.initSet(al, 0xffffffff);

    testing.expectError(error.InvalidBase, a.toString(al, 45));
}

test "big.int string to base 2" {
    const a = try Int.initSet(al, -0b1011);

    const as = try a.toString(al, 2);
    const es = "-1011";

    testing.expect(mem.eql(u8, as, es));
}

test "big.int string to base 16" {
    const a = try Int.initSet(al, 0xefffffff00000001eeeeeeefaaaaaaab);

    const as = try a.toString(al, 16);
    const es = "efffffff00000001eeeeeeefaaaaaaab";

    testing.expect(mem.eql(u8, as, es));
}

test "big.int neg string to" {
    const a = try Int.initSet(al, -123907434);

    const as = try a.toString(al, 10);
    const es = "-123907434";

    testing.expect(mem.eql(u8, as, es));
}

test "big.int zero string to" {
    const a = try Int.initSet(al, 0);

    const as = try a.toString(al, 10);
    const es = "0";

    testing.expect(mem.eql(u8, as, es));
}

test "big.int clone" {
    var a = try Int.initSet(al, 1234);
    const b = try a.clone();

    testing.expect((try a.to(u32)) == 1234);
    testing.expect((try b.to(u32)) == 1234);

    try a.set(77);
    testing.expect((try a.to(u32)) == 77);
    testing.expect((try b.to(u32)) == 1234);
}

test "big.int swap" {
    var a = try Int.initSet(al, 1234);
    var b = try Int.initSet(al, 5678);

    testing.expect((try a.to(u32)) == 1234);
    testing.expect((try b.to(u32)) == 5678);

    a.swap(&b);

    testing.expect((try a.to(u32)) == 5678);
    testing.expect((try b.to(u32)) == 1234);
}

test "big.int to negative" {
    var a = try Int.initSet(al, -10);

    testing.expect((try a.to(i32)) == -10);
}

test "big.int compare" {
    var a = try Int.initSet(al, -11);
    var b = try Int.initSet(al, 10);

    testing.expect(a.cmpAbs(b) == 1);
    testing.expect(a.cmp(b) == -1);
}

test "big.int compare similar" {
    var a = try Int.initSet(al, 0xffffffffeeeeeeeeffffffffeeeeeeee);
    var b = try Int.initSet(al, 0xffffffffeeeeeeeeffffffffeeeeeeef);

    testing.expect(a.cmpAbs(b) == -1);
    testing.expect(b.cmpAbs(a) == 1);
}

test "big.int compare different limb size" {
    var a = try Int.initSet(al, maxInt(Limb) + 1);
    var b = try Int.initSet(al, 1);

    testing.expect(a.cmpAbs(b) == 1);
    testing.expect(b.cmpAbs(a) == -1);
}

test "big.int compare multi-limb" {
    var a = try Int.initSet(al, -0x7777777799999999ffffeeeeffffeeeeffffeeeef);
    var b = try Int.initSet(al, 0x7777777799999999ffffeeeeffffeeeeffffeeeee);

    testing.expect(a.cmpAbs(b) == 1);
    testing.expect(a.cmp(b) == -1);
}

test "big.int equality" {
    var a = try Int.initSet(al, 0xffffffff1);
    var b = try Int.initSet(al, -0xffffffff1);

    testing.expect(a.eqAbs(b));
    testing.expect(!a.eq(b));
}

test "big.int abs" {
    var a = try Int.initSet(al, -5);

    a.abs();
    testing.expect((try a.to(u32)) == 5);

    a.abs();
    testing.expect((try a.to(u32)) == 5);
}

test "big.int negate" {
    var a = try Int.initSet(al, 5);

    a.negate();
    testing.expect((try a.to(i32)) == -5);

    a.negate();
    testing.expect((try a.to(i32)) == 5);
}

test "big.int add single-single" {
    var a = try Int.initSet(al, 50);
    var b = try Int.initSet(al, 5);

    var c = try Int.init(al);
    try c.add(a, b);

    testing.expect((try c.to(u32)) == 55);
}

test "big.int add multi-single" {
    var a = try Int.initSet(al, maxInt(Limb) + 1);
    var b = try Int.initSet(al, 1);

    var c = try Int.init(al);

    try c.add(a, b);
    testing.expect((try c.to(DoubleLimb)) == maxInt(Limb) + 2);

    try c.add(b, a);
    testing.expect((try c.to(DoubleLimb)) == maxInt(Limb) + 2);
}

test "big.int add multi-multi" {
    const op1 = 0xefefefef7f7f7f7f;
    const op2 = 0xfefefefe9f9f9f9f;
    var a = try Int.initSet(al, op1);
    var b = try Int.initSet(al, op2);

    var c = try Int.init(al);
    try c.add(a, b);

    testing.expect((try c.to(u128)) == op1 + op2);
}

test "big.int add zero-zero" {
    var a = try Int.initSet(al, 0);
    var b = try Int.initSet(al, 0);

    var c = try Int.init(al);
    try c.add(a, b);

    testing.expect((try c.to(u32)) == 0);
}

test "big.int add alias multi-limb nonzero-zero" {
    const op1 = 0xffffffff777777771;
    var a = try Int.initSet(al, op1);
    var b = try Int.initSet(al, 0);

    try a.add(a, b);

    testing.expect((try a.to(u128)) == op1);
}

test "big.int add sign" {
    var a = try Int.init(al);

    const one = try Int.initSet(al, 1);
    const two = try Int.initSet(al, 2);
    const neg_one = try Int.initSet(al, -1);
    const neg_two = try Int.initSet(al, -2);

    try a.add(one, two);
    testing.expect((try a.to(i32)) == 3);

    try a.add(neg_one, two);
    testing.expect((try a.to(i32)) == 1);

    try a.add(one, neg_two);
    testing.expect((try a.to(i32)) == -1);

    try a.add(neg_one, neg_two);
    testing.expect((try a.to(i32)) == -3);
}

test "big.int sub single-single" {
    var a = try Int.initSet(al, 50);
    var b = try Int.initSet(al, 5);

    var c = try Int.init(al);
    try c.sub(a, b);

    testing.expect((try c.to(u32)) == 45);
}

test "big.int sub multi-single" {
    var a = try Int.initSet(al, maxInt(Limb) + 1);
    var b = try Int.initSet(al, 1);

    var c = try Int.init(al);
    try c.sub(a, b);

    testing.expect((try c.to(Limb)) == maxInt(Limb));
}

test "big.int sub multi-multi" {
    const op1 = 0xefefefefefefefefefefefef;
    const op2 = 0xabababababababababababab;

    var a = try Int.initSet(al, op1);
    var b = try Int.initSet(al, op2);

    var c = try Int.init(al);
    try c.sub(a, b);

    testing.expect((try c.to(u128)) == op1 - op2);
}

test "big.int sub equal" {
    var a = try Int.initSet(al, 0x11efefefefefefefefefefefef);
    var b = try Int.initSet(al, 0x11efefefefefefefefefefefef);

    var c = try Int.init(al);
    try c.sub(a, b);

    testing.expect((try c.to(u32)) == 0);
}

test "big.int sub sign" {
    var a = try Int.init(al);

    const one = try Int.initSet(al, 1);
    const two = try Int.initSet(al, 2);
    const neg_one = try Int.initSet(al, -1);
    const neg_two = try Int.initSet(al, -2);

    try a.sub(one, two);
    testing.expect((try a.to(i32)) == -1);

    try a.sub(neg_one, two);
    testing.expect((try a.to(i32)) == -3);

    try a.sub(one, neg_two);
    testing.expect((try a.to(i32)) == 3);

    try a.sub(neg_one, neg_two);
    testing.expect((try a.to(i32)) == 1);

    try a.sub(neg_two, neg_one);
    testing.expect((try a.to(i32)) == -1);
}

test "big.int mul single-single" {
    var a = try Int.initSet(al, 50);
    var b = try Int.initSet(al, 5);

    var c = try Int.init(al);
    try c.mul(a, b);

    testing.expect((try c.to(u64)) == 250);
}

test "big.int mul multi-single" {
    var a = try Int.initSet(al, maxInt(Limb));
    var b = try Int.initSet(al, 2);

    var c = try Int.init(al);
    try c.mul(a, b);

    testing.expect((try c.to(DoubleLimb)) == 2 * maxInt(Limb));
}

test "big.int mul multi-multi" {
    const op1 = 0x998888efefefefefefefef;
    const op2 = 0x333000abababababababab;
    var a = try Int.initSet(al, op1);
    var b = try Int.initSet(al, op2);

    var c = try Int.init(al);
    try c.mul(a, b);

    testing.expect((try c.to(u256)) == op1 * op2);
}

test "big.int mul alias r with a" {
    var a = try Int.initSet(al, maxInt(Limb));
    var b = try Int.initSet(al, 2);

    try a.mul(a, b);

    testing.expect((try a.to(DoubleLimb)) == 2 * maxInt(Limb));
}

test "big.int mul alias r with b" {
    var a = try Int.initSet(al, maxInt(Limb));
    var b = try Int.initSet(al, 2);

    try a.mul(b, a);

    testing.expect((try a.to(DoubleLimb)) == 2 * maxInt(Limb));
}

test "big.int mul alias r with a and b" {
    var a = try Int.initSet(al, maxInt(Limb));

    try a.mul(a, a);

    testing.expect((try a.to(DoubleLimb)) == maxInt(Limb) * maxInt(Limb));
}

test "big.int mul a*0" {
    var a = try Int.initSet(al, 0xefefefefefefefef);
    var b = try Int.initSet(al, 0);

    var c = try Int.init(al);
    try c.mul(a, b);

    testing.expect((try c.to(u32)) == 0);
}

test "big.int mul 0*0" {
    var a = try Int.initSet(al, 0);
    var b = try Int.initSet(al, 0);

    var c = try Int.init(al);
    try c.mul(a, b);

    testing.expect((try c.to(u32)) == 0);
}

test "big.int div single-single no rem" {
    var a = try Int.initSet(al, 50);
    var b = try Int.initSet(al, 5);

    var q = try Int.init(al);
    var r = try Int.init(al);
    try Int.divTrunc(&q, &r, a, b);

    testing.expect((try q.to(u32)) == 10);
    testing.expect((try r.to(u32)) == 0);
}

test "big.int div single-single with rem" {
    var a = try Int.initSet(al, 49);
    var b = try Int.initSet(al, 5);

    var q = try Int.init(al);
    var r = try Int.init(al);
    try Int.divTrunc(&q, &r, a, b);

    testing.expect((try q.to(u32)) == 9);
    testing.expect((try r.to(u32)) == 4);
}

test "big.int div multi-single no rem" {
    const op1 = 0xffffeeeeddddcccc;
    const op2 = 34;

    var a = try Int.initSet(al, op1);
    var b = try Int.initSet(al, op2);

    var q = try Int.init(al);
    var r = try Int.init(al);
    try Int.divTrunc(&q, &r, a, b);

    testing.expect((try q.to(u64)) == op1 / op2);
    testing.expect((try r.to(u64)) == 0);
}

test "big.int div multi-single with rem" {
    const op1 = 0xffffeeeeddddcccf;
    const op2 = 34;

    var a = try Int.initSet(al, op1);
    var b = try Int.initSet(al, op2);

    var q = try Int.init(al);
    var r = try Int.init(al);
    try Int.divTrunc(&q, &r, a, b);

    testing.expect((try q.to(u64)) == op1 / op2);
    testing.expect((try r.to(u64)) == 3);
}

test "big.int div multi>2-single" {
    const op1 = 0xfefefefefefefefefefefefefefefefe;
    const op2 = 0xefab8;

    var a = try Int.initSet(al, op1);
    var b = try Int.initSet(al, op2);

    var q = try Int.init(al);
    var r = try Int.init(al);
    try Int.divTrunc(&q, &r, a, b);

    testing.expect((try q.to(u128)) == op1 / op2);
    testing.expect((try r.to(u32)) == 0x3e4e);
}

test "big.int div single-single q < r" {
    var a = try Int.initSet(al, 0x0078f432);
    var b = try Int.initSet(al, 0x01000000);

    var q = try Int.init(al);
    var r = try Int.init(al);
    try Int.divTrunc(&q, &r, a, b);

    testing.expect((try q.to(u64)) == 0);
    testing.expect((try r.to(u64)) == 0x0078f432);
}

test "big.int div single-single q == r" {
    var a = try Int.initSet(al, 10);
    var b = try Int.initSet(al, 10);

    var q = try Int.init(al);
    var r = try Int.init(al);
    try Int.divTrunc(&q, &r, a, b);

    testing.expect((try q.to(u64)) == 1);
    testing.expect((try r.to(u64)) == 0);
}

test "big.int div q=0 alias" {
    var a = try Int.initSet(al, 3);
    var b = try Int.initSet(al, 10);

    try Int.divTrunc(&a, &b, a, b);

    testing.expect((try a.to(u64)) == 0);
    testing.expect((try b.to(u64)) == 3);
}

test "big.int div multi-multi q < r" {
    const op1 = 0x1ffffffff0078f432;
    const op2 = 0x1ffffffff01000000;
    var a = try Int.initSet(al, op1);
    var b = try Int.initSet(al, op2);

    var q = try Int.init(al);
    var r = try Int.init(al);
    try Int.divTrunc(&q, &r, a, b);

    testing.expect((try q.to(u128)) == 0);
    testing.expect((try r.to(u128)) == op1);
}

test "big.int div trunc single-single +/+" {
    const u: i32 = 5;
    const v: i32 = 3;

    var a = try Int.initSet(al, u);
    var b = try Int.initSet(al, v);

    var q = try Int.init(al);
    var r = try Int.init(al);
    try Int.divTrunc(&q, &r, a, b);

    // n = q * d + r
    // 5 = 1 * 3 + 2
    const eq = @divTrunc(u, v);
    const er = @mod(u, v);

    testing.expect((try q.to(i32)) == eq);
    testing.expect((try r.to(i32)) == er);
}

test "big.int div trunc single-single -/+" {
    const u: i32 = -5;
    const v: i32 = 3;

    var a = try Int.initSet(al, u);
    var b = try Int.initSet(al, v);

    var q = try Int.init(al);
    var r = try Int.init(al);
    try Int.divTrunc(&q, &r, a, b);

    //  n = q *  d + r
    // -5 = 1 * -3 - 2
    const eq = -1;
    const er = -2;

    testing.expect((try q.to(i32)) == eq);
    testing.expect((try r.to(i32)) == er);
}

test "big.int div trunc single-single +/-" {
    const u: i32 = 5;
    const v: i32 = -3;

    var a = try Int.initSet(al, u);
    var b = try Int.initSet(al, v);

    var q = try Int.init(al);
    var r = try Int.init(al);
    try Int.divTrunc(&q, &r, a, b);

    // n =  q *  d + r
    // 5 = -1 * -3 + 2
    const eq = -1;
    const er = 2;

    testing.expect((try q.to(i32)) == eq);
    testing.expect((try r.to(i32)) == er);
}

test "big.int div trunc single-single -/-" {
    const u: i32 = -5;
    const v: i32 = -3;

    var a = try Int.initSet(al, u);
    var b = try Int.initSet(al, v);

    var q = try Int.init(al);
    var r = try Int.init(al);
    try Int.divTrunc(&q, &r, a, b);

    //  n = q *  d + r
    // -5 = 1 * -3 - 2
    const eq = 1;
    const er = -2;

    testing.expect((try q.to(i32)) == eq);
    testing.expect((try r.to(i32)) == er);
}

test "big.int div floor single-single +/+" {
    const u: i32 = 5;
    const v: i32 = 3;

    var a = try Int.initSet(al, u);
    var b = try Int.initSet(al, v);

    var q = try Int.init(al);
    var r = try Int.init(al);
    try Int.divFloor(&q, &r, a, b);

    //  n =  q *  d + r
    //  5 =  1 *  3 + 2
    const eq = 1;
    const er = 2;

    testing.expect((try q.to(i32)) == eq);
    testing.expect((try r.to(i32)) == er);
}

test "big.int div floor single-single -/+" {
    const u: i32 = -5;
    const v: i32 = 3;

    var a = try Int.initSet(al, u);
    var b = try Int.initSet(al, v);

    var q = try Int.init(al);
    var r = try Int.init(al);
    try Int.divFloor(&q, &r, a, b);

    //  n =  q *  d + r
    // -5 = -2 *  3 + 1
    const eq = -2;
    const er = 1;

    testing.expect((try q.to(i32)) == eq);
    testing.expect((try r.to(i32)) == er);
}

test "big.int div floor single-single +/-" {
    const u: i32 = 5;
    const v: i32 = -3;

    var a = try Int.initSet(al, u);
    var b = try Int.initSet(al, v);

    var q = try Int.init(al);
    var r = try Int.init(al);
    try Int.divFloor(&q, &r, a, b);

    //  n =  q *  d + r
    //  5 = -2 * -3 - 1
    const eq = -2;
    const er = -1;

    testing.expect((try q.to(i32)) == eq);
    testing.expect((try r.to(i32)) == er);
}

test "big.int div floor single-single -/-" {
    const u: i32 = -5;
    const v: i32 = -3;

    var a = try Int.initSet(al, u);
    var b = try Int.initSet(al, v);

    var q = try Int.init(al);
    var r = try Int.init(al);
    try Int.divFloor(&q, &r, a, b);

    //  n =  q *  d + r
    // -5 =  2 * -3 + 1
    const eq = 1;
    const er = -2;

    testing.expect((try q.to(i32)) == eq);
    testing.expect((try r.to(i32)) == er);
}

test "big.int div multi-multi with rem" {
    var a = try Int.initSet(al, 0x8888999911110000ffffeeeeddddccccbbbbaaaa9999);
    var b = try Int.initSet(al, 0x99990000111122223333);

    var q = try Int.init(al);
    var r = try Int.init(al);
    try Int.divTrunc(&q, &r, a, b);

    testing.expect((try q.to(u128)) == 0xe38f38e39161aaabd03f0f1b);
    testing.expect((try r.to(u128)) == 0x28de0acacd806823638);
}

test "big.int div multi-multi no rem" {
    var a = try Int.initSet(al, 0x8888999911110000ffffeeeedb4fec200ee3a4286361);
    var b = try Int.initSet(al, 0x99990000111122223333);

    var q = try Int.init(al);
    var r = try Int.init(al);
    try Int.divTrunc(&q, &r, a, b);

    testing.expect((try q.to(u128)) == 0xe38f38e39161aaabd03f0f1b);
    testing.expect((try r.to(u128)) == 0);
}

test "big.int div multi-multi (2 branch)" {
    var a = try Int.initSet(al, 0x866666665555555588888887777777761111111111111111);
    var b = try Int.initSet(al, 0x86666666555555554444444433333333);

    var q = try Int.init(al);
    var r = try Int.init(al);
    try Int.divTrunc(&q, &r, a, b);

    testing.expect((try q.to(u128)) == 0x10000000000000000);
    testing.expect((try r.to(u128)) == 0x44444443444444431111111111111111);
}

test "big.int div multi-multi (3.1/3.3 branch)" {
    var a = try Int.initSet(al, 0x11111111111111111111111111111111111111111111111111111111111111);
    var b = try Int.initSet(al, 0x1111111111111111111111111111111111111111171);

    var q = try Int.init(al);
    var r = try Int.init(al);
    try Int.divTrunc(&q, &r, a, b);

    testing.expect((try q.to(u128)) == 0xfffffffffffffffffff);
    testing.expect((try r.to(u256)) == 0x1111111111111111111110b12222222222222222282);
}

test "big.int shift-right single" {
    var a = try Int.initSet(al, 0xffff0000);
    try a.shiftRight(a, 16);

    testing.expect((try a.to(u32)) == 0xffff);
}

test "big.int shift-right multi" {
    var a = try Int.initSet(al, 0xffff0000eeee1111dddd2222cccc3333);
    try a.shiftRight(a, 67);

    testing.expect((try a.to(u64)) == 0x1fffe0001dddc222);
}

test "big.int shift-left single" {
    var a = try Int.initSet(al, 0xffff);
    try a.shiftLeft(a, 16);

    testing.expect((try a.to(u64)) == 0xffff0000);
}

test "big.int shift-left multi" {
    var a = try Int.initSet(al, 0x1fffe0001dddc222);
    try a.shiftLeft(a, 67);

    testing.expect((try a.to(u128)) == 0xffff0000eeee11100000000000000000);
}

test "big.int shift-right negative" {
    var a = try Int.init(al);

    try a.shiftRight(try Int.initSet(al, -20), 2);
    testing.expect((try a.to(i32)) == -20 >> 2);

    try a.shiftRight(try Int.initSet(al, -5), 10);
    testing.expect((try a.to(i32)) == -5 >> 10);
}

test "big.int shift-left negative" {
    var a = try Int.init(al);

    try a.shiftRight(try Int.initSet(al, -10), 1232);
    testing.expect((try a.to(i32)) == -10 >> 1232);
}

test "big.int bitwise and simple" {
    var a = try Int.initSet(al, 0xffffffff11111111);
    var b = try Int.initSet(al, 0xeeeeeeee22222222);

    try a.bitAnd(a, b);

    testing.expect((try a.to(u64)) == 0xeeeeeeee00000000);
}

test "big.int bitwise and multi-limb" {
    var a = try Int.initSet(al, maxInt(Limb) + 1);
    var b = try Int.initSet(al, maxInt(Limb));

    try a.bitAnd(a, b);

    testing.expect((try a.to(u128)) == 0);
}

test "big.int bitwise xor simple" {
    var a = try Int.initSet(al, 0xffffffff11111111);
    var b = try Int.initSet(al, 0xeeeeeeee22222222);

    try a.bitXor(a, b);

    testing.expect((try a.to(u64)) == 0x1111111133333333);
}

test "big.int bitwise xor multi-limb" {
    var a = try Int.initSet(al, maxInt(Limb) + 1);
    var b = try Int.initSet(al, maxInt(Limb));

    try a.bitXor(a, b);

    testing.expect((try a.to(DoubleLimb)) == (maxInt(Limb) + 1) ^ maxInt(Limb));
}

test "big.int bitwise or simple" {
    var a = try Int.initSet(al, 0xffffffff11111111);
    var b = try Int.initSet(al, 0xeeeeeeee22222222);

    try a.bitOr(a, b);

    testing.expect((try a.to(u64)) == 0xffffffff33333333);
}

test "big.int bitwise or multi-limb" {
    var a = try Int.initSet(al, maxInt(Limb) + 1);
    var b = try Int.initSet(al, maxInt(Limb));

    try a.bitOr(a, b);

    // TODO: big.int.cpp or is wrong on multi-limb.
    testing.expect((try a.to(DoubleLimb)) == (maxInt(Limb) + 1) + maxInt(Limb));
}

test "big.int var args" {
    var a = try Int.initSet(al, 5);

    try a.add(a, try Int.initSet(al, 6));
    testing.expect((try a.to(u64)) == 11);

    testing.expect(a.cmp(try Int.initSet(al, 11)) == 0);
    testing.expect(a.cmp(try Int.initSet(al, 14)) <= 0);
}

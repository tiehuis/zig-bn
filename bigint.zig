// TODO:
// - multi-limb division
// - confirm what behavior we want for shift on negative values

const std = @import("std");
const builtin = @import("builtin");
const debug = std.debug;
const math = std.math;
const mem = std.mem;
const Allocator = mem.Allocator;
const ArrayList = std.ArrayList;

const TypeId = builtin.TypeId;

const Limb = u32;
const Log2Limb = math.Log2Int(Limb);
const DoubleLimb = @IntType(false, 2 * Limb.bit_count);

pub const BigInt = struct {
    positive: bool,
    //  - little-endian ordered
    //  - limbs.len >= 1 always
    //  - zero value -> limbs.len == 1 with limbs.items[0] == 0
    limbs: ArrayList(Limb),

    pub fn init(allocator: &Allocator) !BigInt {
        return BigInt {
            .positive = false,
            .limbs = block: {
                var limbs = ArrayList(Limb).init(allocator);
                try limbs.append(0);
                break :block limbs;
            },
        };
    }

    pub fn initSet(allocator: &Allocator, value: var) !BigInt {
        var s = try BigInt.init(allocator);
        try s.set(value);
        return s;
    }

    pub fn initCapacity(allocator: &Allocator, capacity: usize) !BigInt {
        return BigInt {
            .positive = false,
            .limbs = block: {
                var limbs = ArrayList(Limb).init(allocator);
                try limbs.ensureCapacity(capacity);
                try limbs.append(0);
                break :block limbs;
            },
        };
    }

    pub fn ensureCapacity(self: &BigInt, capacity: usize) !void {
        try self.limbs.ensureCapacity(capacity);
    }

    pub fn deinit(self: &const BigInt) void {
        self.limbs.deinit();
    }

    pub fn clone(other: &const BigInt) !BigInt {
        return BigInt {
            .positive = other.positive,
            .limbs = block: {
                var limbs = ArrayList(Limb).init(other.limbs.allocator);
                try limbs.appendSlice(other.limbs.toSliceConst());
                break :block limbs;
            },
        };
    }

    pub fn copy(self: &BigInt, other: &const BigInt) !void {
        self.positive = other.positive;
        self.limbs.len = 0;
        self.limbs.shrink(0);
        try self.limbs.appendSlice(other.limbs.toSliceConst());
    }

    pub fn swap(self: &BigInt, other: &BigInt) void {
        mem.swap(bool, &self.positive, &other.positive);
        mem.swap(ArrayList(Limb), &self.limbs, &other.limbs);
    }

    pub fn dump(self: &const BigInt) void {
        for (self.limbs.toSliceConst()) |limb| {
            std.debug.warn("{x} ", limb);
        }
        std.debug.warn("\n");
    }

    pub fn negate(r: &BigInt) void {
        r.positive = !r.positive;
    }

    pub fn abs(r: &BigInt) void {
        r.positive = true;
    }

    pub fn set(self: &BigInt, value: var) Allocator.Error!void {
        const T = @typeOf(value);

        switch (@typeInfo(T)) {
            TypeId.Int => |info| {
                self.positive = value >= 0;
                self.limbs.shrink(0);

                var w_value = if (value < 0) -value else value;

                if (info.bits <= Limb.bit_count) {
                    try self.limbs.append(Limb(value));
                } else {
                    while (w_value != 0) {
                        try self.limbs.append(@truncate(Limb, w_value));
                        w_value >>= Limb.bit_count;
                    }
                }
            },
            TypeId.IntLiteral => {
                self.positive = value >= 0;
                self.limbs.shrink(0);

                comptime var w_value = if (value < 0) -value else value;

                if (w_value <= @maxValue(Limb)) {
                    try self.limbs.append(w_value);
                } else {
                    inline while (w_value != 0) {
                        const mask = (1 << Limb.bit_count) - 1;
                        try self.limbs.append(w_value & mask);
                        w_value >>= Limb.bit_count;
                    }
                }
            },
            else => {
                @compileError("cannot set BigInt using type " ++ @typeName(T));
            },
        }
    }

    const ConvertError = error{
        NegativeIntoUnsigned,
        TargetTooSmall,
    };

    pub fn to(self: &const BigInt, comptime T: type) ConvertError!T {
        switch (@typeId(T)) {
            TypeId.Int => {
                // We need the extra 32-bytes due to the way the ArrayList ensureCapacity function
                // over-allocates. Consider adding an ensureExactCapacity or some variant.
                // This would fail on very large T right now.
                //
                // TODO: Use a @clz and check if it fits instead. Avoids the compare since we
                // know any integer type is a power of two. Avoids the stack allocation as well.
                // Can handle the signed requirement by simply checking the twos-complement.
                var buffer: [T.bit_count / Limb.bit_count + 1 + 32]u8 = undefined;
                var stack = std.heap.FixedBufferAllocator.init(buffer[0..]);
                var max_t_size = BigInt.initSet(&stack.allocator, @maxValue(T)) catch unreachable;

                // TODO: Minimum negative value will fail here even if okay.
                if (self.cmp(max_t_size) > 0) {
                    return error.TargetTooSmall;
                }

                var r: T = 0;

                if (@sizeOf(T) <= @sizeOf(Limb)) {
                    r = T(self.limbs.items[0]);
                } else {
                    for (self.limbs.toSliceConst()) |_, ri| {
                        const limb = self.limbs.at(self.limbs.len - ri - 1);
                        r <<= Limb.bit_count;
                        r |= limb;
                    }
                }

                if (!T.is_signed) {
                    return if (self.positive) r else error.NegativeIntoUnsigned;
                } else {
                    return if (self.positive) r else -r;
                }
            },
            else => {
                @compileError("cannot convert BigInt to type " ++ @typeName(T));
            },
        }
    }

    fn charToDigit(ch: u8, base: u8) !u8 {
        const d = switch (ch) {
            '0' ... '9' => ch - '0',
            'a' ... 'f' => (ch - 'a') + 0xa,
            else => return error.InvalidCharForDigit,
        };

        return if (d < base) d else return error.DigitTooLargeForBase;
    }

    fn digitToChar(d: u8, base: u8) !u8 {
        if (d >= base) {
            return error.DigitTooLargeForBase;
        }

        return switch (d) {
            0 ... 9 => '0' + d,
            0xa ... 0xf => ('a' - 0xa) + d,
            else => unreachable,
        };
    }

    pub fn setString(self: &BigInt, base: u8, value: []const u8) !void {
        if (base < 2 or base > 16) {
            return error.InvalidBase;
        }

        var i: usize = 0;
        if (value.len > 0 and value[0] == '-') {
            self.positive = false;
            i += 1;
        } else {
            self.positive = true;
        }

        // TODO: We need to over-allocate here due to the way ArrayList works.
        var buffer: [64]u8 = undefined;
        var stack = std.heap.FixedBufferAllocator.init(buffer[0..]);
        var b = try BigInt.initSet(&stack.allocator, base);
        var p = try BigInt.init(&stack.allocator);

        // TODO: Can specialize power of twos into a shift instead of a mul. Can also
        // pre-allocate space required.
        try self.set(0);
        for (value[i..]) |ch| {
            const d = try charToDigit(ch, base);
            try p.set(d);

            try self.mul(self, &b);
            try self.add(self, &p);
        }
    }

    pub fn toString(self: &const BigInt, allocator: &Allocator, base: u8) ![]const u8 {
        if (base < 2 or base > 16) {
            return error.InvalidBase;
        }

        var digits = ArrayList(u8).init(allocator);
        defer digits.deinit();

        if (self.eqZero()) {
            try digits.append('0');
            return digits.toOwnedSlice();
        }

        // Power of two: can do a single pass and use masks to extract digits.
        if (base & (base - 1) == 0) {
            const base_shift = math.log2_int(Limb, base);

            for (self.limbs.toSliceConst()) |limb| {
                var shift: usize = 0;
                while (shift < Limb.bit_count) : (shift += base_shift) {
                    const r = u8((limb >> Log2Limb(shift)) & Limb(base - 1));
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
        }
        // Non power-of-two: need to perform slow division.
        //
        // TODO: Combine divisions and perform sub-divisions using machine-word.
        else {
            var q = try self.clone();
            q.positive = true;
            var r = try BigInt.init(allocator);
            var b = try BigInt.initSet(allocator, base);

            while (!q.eqZero()) {
                try BigInt.div(&q, &r, &q, &b);
                const ch = try digitToChar(try r.to(u8), base);
                try digits.append(ch);
            }
        }

        if (!self.positive) {
            try digits.append('-');
        }

        var s = digits.toOwnedSlice();
        mem.reverse(u8, s);
        return s;
    }

    // returns -1, 0, 1 if |a| < |b|, |a| == |b| or |a| > |b| respectively.
    pub fn cmpAbs(a: &const BigInt, b: &const BigInt) i8 {
        if (a.limbs.len < b.limbs.len) {
            return -1;
        }
        if (a.limbs.len > b.limbs.len) {
            return 1;
        }

        var i: usize = a.limbs.len - 1;
        while (i != 0) : (i -= 1) {
            if (a.limbs.items[i] != b.limbs.items[i]) {
                break;
            }
        }

        if (a.limbs.items[i] < b.limbs.items[i]) {
            return -1;
        } else if (a.limbs.items[i] > b.limbs.items[i]) {
            return 1;
        } else {
            return 0;
        }
    }

    // returns -1, 0, 1 if a < b, a == b or a > b respectively.
    pub fn cmp(a: &const BigInt, b: &const BigInt) i8 {
        if (a.positive != b.positive) {
            return if (a.positive) i8(1) else -1;
        } else {
            const r = cmpAbs(a, b);
            return if (a.positive) r else -r;
        }
    }

    // if a == 0
    pub fn eqZero(a: &const BigInt) bool {
        return a.limbs.len == 1 and a.limbs.items[0] == 0;
    }

    // if |a| == |b|
    pub fn eqAbs(a: &const BigInt, b: &const BigInt) bool {
        return cmpAbs(a, b) == 0;
    }

    // if a == b
    pub fn eq(a: &const BigInt, b: &const BigInt) bool {
        return cmp(a, b) == 0;
    }

    // Normalize for a possible single carry digit.
    //
    // [1, 2, 3, 4, 0] -> [1, 2, 3, 4]
    // [1, 2, 3, 4, 5] -> [1, 2, 3, 4]
    // [0]             -> [0]
    fn norm1(r: &BigInt, length: usize) void {
        std.debug.assert(length > 0);

        if (r.limbs.items[length - 1] == 0) {
            std.debug.assert(length == 1 or r.limbs.items[length - 2] != 0);
            r.limbs.len = length - 1;
        } else {
            r.limbs.len = length;
        }
    }

    // Normalize a possible sequence of leading zeros.
    //
    // [1, 2, 3, 4, 0] -> [1, 2, 3, 4]
    // [1, 2, 0, 0, 0] -> [1, 2]
    // [0, 0, 0, 0, 0] -> [0]
    fn normN(r: &BigInt, length: usize) void {
        std.debug.assert(length > 0);

        var j = length;
        while (j > 0) : (j -= 1) {
            if (r.limbs.items[j - 1] != 0) {
                break;
            }
        }

        // zero is represented as a length 1 limb.
        r.limbs.len = if (j != 0) j else 1;
    }

    // r = a + b
    pub fn add(r: &BigInt, a: &const BigInt, b: &const BigInt) Allocator.Error!void {
        if (a.eqZero()) {
            if (r != b) {
                try r.copy(b);
            }
            return;
        } else if (b.eqZero()) {
            if (r != a) {
                try r.copy(a);
            }
            return;
        }

        if (a.positive != b.positive) {
            if (a.positive) {
                // (a) + (-b) => a - b
                try r.sub(a, b);
            } else {
                // (-a) + (b) => b - a
                try r.sub(a, b);
            }
        } else {
            if (a.limbs.len >= b.limbs.len) {
                try r.limbs.ensureCapacity(a.limbs.len + 1);
                lladd(r.limbs.items[0..], a.limbs.toSliceConst(), b.limbs.toSliceConst());
                r.norm1(a.limbs.len + 1);
            } else {
                try r.limbs.ensureCapacity(b.limbs.len + 1);
                lladd(r.limbs.items[0..], b.limbs.toSliceConst(), a.limbs.toSliceConst());
                r.norm1(b.limbs.len + 1);
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
            c += Limb(@addWithOverflow(Limb, a[i], b[i], &r[i]));
            c += Limb(@addWithOverflow(Limb, r[i], carry, &r[i]));
            carry = c;
        }

        while (i < a.len) : (i += 1) {
            carry = Limb(@addWithOverflow(Limb, a[i], carry, &r[i]));
        }

        r[i] = carry;
    }

    // r = a - b
    pub fn sub(r: &BigInt, a: &const BigInt, b: &const BigInt) !void {
        if (a.positive != b.positive) {
            if (a.positive) {
                // (a) - (-b) => a + b
                try r.add(a, b);
            } else {
                // (-a) - (b) => -(a + b)
                try r.add(a, b);
                r.positive = false;
            }
        } else {
            if (a.cmp(b) >= 0) {
                try r.limbs.ensureCapacity(a.limbs.len + 1);
                llsub(r.limbs.items[0..], a.limbs.toSliceConst(), b.limbs.toSliceConst());
                r.normN(a.limbs.len);
            } else {
                try r.limbs.ensureCapacity(b.limbs.len + 1);
                llsub(r.limbs.items[0..], b.limbs.toSliceConst(), a.limbs.toSliceConst());
                r.normN(b.limbs.len);
            }

            r.positive = a.positive;
        }
    }

    // Knuth 4.3.1, Algorithm S.
    //
    // Returns the length of rop.
    fn llsub(r: []Limb, a: []const Limb, b: []const Limb) void {
        @setRuntimeSafety(false);
        debug.assert(a.len != 0 and b.len != 0);
        debug.assert(a.len > b.len or (a.len == b.len and a[a.len - 1] >= b[b.len - 1]));
        debug.assert(r.len >= a.len);

        var i: usize = 0;
        var borrow: Limb = 0;

        while (i < b.len) : (i += 1) {
            var c: Limb = 0;
            c += Limb(@subWithOverflow(Limb, a[i], b[i], &r[i]));
            c += Limb(@subWithOverflow(Limb, r[i], borrow, &r[i]));
            borrow = c;
        }

        while (i < a.len) : (i += 1) {
            borrow = Limb(@subWithOverflow(Limb, a[i], borrow, &r[i]));
        }

        debug.assert(borrow == 0);
    }

    // rma = a * b
    //
    // For greatest efficiency, ensure rma does not alias a or b.
    pub fn mul(rma: &BigInt, a: &const BigInt, b: &const BigInt) !void {
        var r = rma;
        var aliased = rma == a or rma == b;

        var sr: BigInt = undefined;
        if (aliased) {
            sr = try BigInt.initCapacity(rma.limbs.allocator, a.limbs.len + b.limbs.len);
            r = &sr;
            aliased = true;
        }
        defer if (aliased) {
            rma.swap(r);
            r.deinit();
        };

        try r.limbs.ensureCapacity(a.limbs.len + b.limbs.len);

        if (a.limbs.len >= b.limbs.len) {
            llmul(r.limbs.items[0..], a.limbs.toSliceConst(), b.limbs.toSliceConst());
        } else {
            llmul(r.limbs.items[0..], b.limbs.toSliceConst(), a.limbs.toSliceConst());
        }

        r.positive = a.positive == b.positive;
        r.normN(a.limbs.len + b.limbs.len);
    }

    // a + b * c + *carry, sets carry to the overflow bits
    pub fn addMulLimbWithCarry(a: Limb, b: Limb, c: Limb, carry: &Limb) Limb {
        var r1: Limb = undefined;

        // r1 = a + *carry
        const c1 = Limb(@addWithOverflow(Limb, a, *carry, &r1));

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
        const c3 = Limb(@addWithOverflow(Limb, r1, r2, &r1));

        // This never overflows, c1, c3 are either 0 or 1 and if both are 1 then
        // c2 is at least <= @maxValue(Limb) - 2.
        *carry = c1 + c2 + c3;

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
                r[i+j] = @inlineCall(addMulLimbWithCarry, r[i+j], a[i], b[j], &carry);
            }
            r[i+j] = carry;
        }
    }

    // quo = a / b (rem rem)
    pub fn div(quo: &BigInt, rem: &BigInt, a: &const BigInt, b: &const BigInt) !void {
        if (b.eqZero()) {
            @panic("division by zero");
        }

        if (a.cmpAbs(b) < 0) {
            // quo may alias a so handle rem first
            if (rem != a) {
                try rem.copy(a);
                rem.positive = a.positive == b.positive;
            }

            quo.positive = true;
            quo.limbs.len = 1;
            quo.limbs.items[0] = 0;
            return;
        }

        if (b.limbs.len == 1) {
            try quo.limbs.ensureCapacity(a.limbs.len);

            lldiv1(quo.limbs.items[0..], &rem.limbs.items[0], a.limbs.toSliceConst(), b.limbs.items[0]);
            quo.norm1(a.limbs.len);
            quo.positive = a.positive == b.positive;

            rem.limbs.len = 1;
            rem.positive = true;
        } else {
            try quo.limbs.ensureCapacity(a.limbs.len);
            try rem.limbs.ensureCapacity(b.limbs.len);

            lldivN(quo.limbs.items[0..], rem.limbs.items[0..], a.limbs.toSliceConst(), b.limbs.toSliceConst());
            quo.normN(a.limbs.len);
            quo.positive = a.positive == b.positive;

            rem.normN(b.limbs.len);
            rem.positive = true;
        }
    }

    // Knuth 4.3.1, Exercise 16.
    fn lldiv1(quo: []Limb, rem: &Limb, a: []const Limb, b: Limb) void {
        @setRuntimeSafety(false);
        debug.assert(a.len > 1 or a[0] >= b);
        debug.assert(quo.len >= a.len);

        *rem = 0;
        for (a) |_, ri| {
            const i = a.len - ri - 1;
            const pdiv = ((DoubleLimb(*rem) << Limb.bit_count) | a[i]);

            if (pdiv == 0) {
                quo[i] = 0;
                *rem = 0;
            } else if (pdiv < b) {
                quo[i] = 0;
                *rem = @truncate(Limb, pdiv);
            } else if (pdiv == b) {
                quo[i] = 1;
                *rem = 0;
            } else {
                quo[i] = @truncate(Limb, @divFloor(pdiv, b));
                *rem = @truncate(Limb, pdiv - (quo[i] *% b));
            }
        }
    }

    // Knuth 4.3.1, Algorithm D.
    //
    // quo, a and b MUST NOT alias
    fn lldivN(quo: []Limb, rem: []Limb, a: []const Limb, b: []const Limb) void {
        debug.assert(a.ptr != b.ptr and a.ptr != quo.ptr and b.ptr != quo.ptr);
        debug.assert(a.len >= b.len);
        debug.assert(b.len >= 2);

        @panic("TODO: implement multi-limb division");
    }

    // r = a << shift, in other words, r = a * 2^shift
    pub fn shiftLeft(r: &BigInt, a: &const BigInt, shift: usize) !void {
        try r.limbs.ensureCapacity(a.limbs.len + (shift / Limb.bit_count) + 1);
        llshl(r.limbs.items[0..], a.limbs.toSliceConst(), shift);
        r.norm1(a.limbs.len + (shift / Limb.bit_count) + 1);
        r.positive = a.positive;
    }

    fn llshl(r: []Limb, a: []const Limb, shift: usize) void {
        @setRuntimeSafety(false);
        debug.assert(a.len >= 1);
        debug.assert(r.len >= a.len + (shift / Limb.bit_count) + 1);

        const limb_shift = shift / Limb.bit_count + 1;
        const interior_limb_shift = Log2Limb(shift % Limb.bit_count);

        var carry: Limb = 0;
        var i: usize = 0;
        while (i < a.len) : (i += 1) {
            const src_i = a.len - i - 1;
            const dst_i = src_i + limb_shift;

            const src_digit = a[src_i];
            r[dst_i] = carry | @inlineCall(math.shr, Limb, src_digit, Limb.bit_count - Limb(interior_limb_shift));
            carry = (src_digit << interior_limb_shift);
        }

        r[limb_shift - 1] = carry;
        mem.set(Limb, r[0 .. limb_shift - 1], 0);
    }

    // r = a >> shift
    pub fn shiftRight(r: &BigInt, a: &const BigInt, shift: usize) !void {
        if (a.limbs.len <= shift / Limb.bit_count) {
            r.limbs.len = 1;
            r.limbs.items[0] = 0;
            r.positive = true;
            return;
        }

        try r.limbs.ensureCapacity(a.limbs.len - (shift / Limb.bit_count));
        const r_len = llshr(r.limbs.items[0..], a.limbs.toSliceConst(), shift);
        r.limbs.len = a.limbs.len - (shift / Limb.bit_count);
        r.positive = a.positive;
    }

    fn llshr(r: []Limb, a: []const Limb, shift: usize) void {
        @setRuntimeSafety(false);
        debug.assert(a.len >= 1);
        debug.assert(r.len >= a.len - (shift / Limb.bit_count));

        const limb_shift = shift / Limb.bit_count;
        const interior_limb_shift = Log2Limb(shift % Limb.bit_count);

        var carry: Limb = 0;
        var i: usize = 0;
        while (i < a.len - limb_shift) : (i += 1) {
            const src_i = a.len - i - 1;
            const dst_i = src_i - limb_shift;

            const src_digit = a[src_i];
            r[dst_i] = carry | (src_digit >> interior_limb_shift);
            carry = @inlineCall(math.shl, Limb, src_digit, Limb.bit_count - Limb(interior_limb_shift));
        }
    }

    // r = a | b
    pub fn bitOr(r: &BigInt, a: &const BigInt, b: &const BigInt) !void {
        if (a.limbs.len > b.limbs.len) {
            try r.limbs.ensureCapacity(a.limbs.len);
            llor(r.limbs.items[0..], a.limbs.toSliceConst(), b.limbs.toSliceConst());
            r.limbs.len = a.limbs.len;
        } else {
            try r.limbs.ensureCapacity(b.limbs.len);
            llor(r.limbs.items[0..], b.limbs.toSliceConst(), a.limbs.toSliceConst());
            r.limbs.len = b.limbs.len;
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
    pub fn bitAnd(r: &BigInt, a: &const BigInt, b: &const BigInt) !void {
        if (a.limbs.len > b.limbs.len) {
            try r.limbs.ensureCapacity(b.limbs.len);
            const r_len = lland(r.limbs.items[0..], a.limbs.toSliceConst(), b.limbs.toSliceConst());
            r.normN(b.limbs.len);
        } else {
            try r.limbs.ensureCapacity(a.limbs.len);
            const r_len = lland(r.limbs.items[0..], b.limbs.toSliceConst(), a.limbs.toSliceConst());
            r.normN(a.limbs.len);
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
    pub fn bitXor(r: &BigInt, a: &const BigInt, b: &const BigInt) !void {
        if (a.limbs.len > b.limbs.len) {
            try r.limbs.ensureCapacity(a.limbs.len);
            const r_len = llxor(r.limbs.items[0..], a.limbs.toSliceConst(), b.limbs.toSliceConst());
            r.normN(a.limbs.len);
        } else {
            try r.limbs.ensureCapacity(b.limbs.len);
            const r_len = llxor(r.limbs.items[0..], b.limbs.toSliceConst(), a.limbs.toSliceConst());
            r.normN(b.limbs.len);
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

var al = debug.global_allocator;

test "bigint comptime_int set" {
    var a = try BigInt.initSet(al, 0xefffffff00000001eeeeeeefaaaaaaab);

    debug.assert(a.limbs.items[0] == 0xaaaaaaab);
    debug.assert(a.limbs.items[1] == 0xeeeeeeef);
    debug.assert(a.limbs.items[2] == 0x00000001);
    debug.assert(a.limbs.items[3] == 0xefffffff);
}

test "bigint comptime_int set negative" {
    var a = try BigInt.initSet(al, -10);

    debug.assert(a.limbs.items[0] == 10);
    debug.assert(a.positive == false);
}

test "bigint comptime_int to" {
    const a = try BigInt.initSet(al, 0xefffffff00000001eeeeeeefaaaaaaab);

    debug.assert((try a.to(u128)) == 0xefffffff00000001eeeeeeefaaaaaaab);
}

test "bigint sub-limb to" {
    const a = try BigInt.initSet(al, 10);

    debug.assert((try a.to(u8)) == 10);
}

test "bigint string set" {
    var a = try BigInt.init(al);
    try a.setString(10, "120317241209124781241290847124");

    debug.assert((try a.to(u128)) == 120317241209124781241290847124);
}

test "bigint string to" {
    const a = try BigInt.initSet(al, 120317241209124781241290847124);

    const as = try a.toString(al, 10);
    const es = "120317241209124781241290847124";

    debug.assert(mem.eql(u8, as, es));
}

test "bigint string to base 2" {
    const a = try BigInt.initSet(al, -0b1011);

    const as = try a.toString(al, 2);
    const es = "-1011";

    debug.assert(mem.eql(u8, as, es));
}

test "bigint string to base 16" {
    const a = try BigInt.initSet(al, 0xefffffff00000001eeeeeeefaaaaaaab);

    const as = try a.toString(al, 16);
    const es = "efffffff00000001eeeeeeefaaaaaaab";

    debug.assert(mem.eql(u8, as, es));
}

test "bigint neg string to" {
    const a = try BigInt.initSet(al, -123907434);

    const as = try a.toString(al, 10);
    const es = "-123907434";

    debug.assert(mem.eql(u8, as, es));
}

test "bigint zero string to" {
    const a = try BigInt.initSet(al, 0);

    const as = try a.toString(al, 10);
    const es = "0";

    debug.assert(mem.eql(u8, as, es));
}

test "bigint clone" {
    var a = try BigInt.initSet(al, 1234);
    const b = try a.clone();

    debug.assert((try a.to(u32)) == 1234);
    debug.assert((try b.to(u32)) == 1234);

    try a.set(77);
    debug.assert((try a.to(u32)) == 77);
    debug.assert((try b.to(u32)) == 1234);
}

test "bigint swap" {
    var a = try BigInt.initSet(al, 1234);
    var b = try BigInt.initSet(al, 5678);

    debug.assert((try a.to(u32)) == 1234);
    debug.assert((try b.to(u32)) == 5678);

    a.swap(&b);

    debug.assert((try a.to(u32)) == 5678);
    debug.assert((try b.to(u32)) == 1234);
}

test "bigint to negative" {
    var a = try BigInt.initSet(al, -10);

    debug.assert((try a.to(i32)) == -10);
}

test "bigint compare" {
    var a = try BigInt.initSet(al, -11);
    var b = try BigInt.initSet(al, 10);

    debug.assert(a.cmpAbs(&b) == 1);
    debug.assert(a.cmp(&b) == -1);
}

test "bigint compare multi-limb" {
    var a = try BigInt.initSet(al, -0xffffeeeeffffeeeeffffeeeef);
    var b = try BigInt.initSet(al, 0xffffeeeeffffeeeeffffeeeee);

    debug.assert(a.cmpAbs(&b) == 1);
    debug.assert(a.cmp(&b) == -1);
 }

test "bigint equality" {
    var a = try BigInt.initSet(al, 0xffffffff1);
    var b = try BigInt.initSet(al, -0xffffffff1);

    debug.assert(a.eqAbs(&b));
    debug.assert(!a.eq(&b));
}

test "bigint abs" {
    var a = try BigInt.initSet(al, -5);

    a.abs();
    debug.assert((try a.to(u32)) == 5);

    a.abs();
    debug.assert((try a.to(u32)) == 5);
}

test "bigint negate" {
    var a = try BigInt.initSet(al, 5);

    a.negate();
    debug.assert((try a.to(i32)) == -5);

    a.negate();
    debug.assert((try a.to(i32)) == 5);
}

test "bigint add single-single" {
    var a = try BigInt.initSet(al, 50);
    var b = try BigInt.initSet(al, 5);

    var c = try BigInt.init(al);
    try c.add(&a, &b);

    debug.assert((try c.to(u32)) == 55);
}

test "bigint add multi-single" {
    var a = try BigInt.initSet(al, 0xffffffff);
    var b = try BigInt.initSet(al, 1);

    var c = try BigInt.init(al);
    try c.add(&a, &b);

    debug.assert((try c.to(u64)) == 0x100000000);
}

test "bigint add multi-multi" {
    var a = try BigInt.initSet(al, 0xefefefef7f7f7f7f);
    var b = try BigInt.initSet(al, 0xfefefefe9f9f9f9f);

    var c = try BigInt.init(al);
    try c.add(&a, &b);

    debug.assert((try c.to(u128)) == 0x1eeeeeeee1f1f1f1e);
}

test "bigint add zero-zero" {
    var a = try BigInt.initSet(al, 0);
    var b = try BigInt.initSet(al, 0);

    var c = try BigInt.init(al);
    try c.add(&a, &b);

    debug.assert((try c.to(u32)) == 0);
}

test "bigint add alias multi-limb nonzero-zero" {
    var a = try BigInt.initSet(al, 123123019724124);
    var b = try BigInt.initSet(al, 0);

    try a.add(&a, &b);

    debug.assert((try a.to(u128)) == 123123019724124);
}

test "bigint sub single-single" {
    var a = try BigInt.initSet(al, 50);
    var b = try BigInt.initSet(al, 5);

    var c = try BigInt.init(al);
    try c.sub(&a, &b);

    debug.assert((try c.to(u32)) == 45);
}

test "bigint sub multi-single" {
    var a = try BigInt.initSet(al, 0x100000000);
    var b = try BigInt.initSet(al, 1);

    var c = try BigInt.init(al);
    try c.sub(&a, &b);

    debug.assert((try c.to(u64)) == 0xffffffff);
}

test "bigint sub multi-multi" {
    var a = try BigInt.initSet(al, 0xefefefefefefefefefefefef);
    var b = try BigInt.initSet(al, 0xabababababababababababab);

    var c = try BigInt.init(al);
    try c.sub(&a, &b);

    debug.assert((try c.to(u128)) == 0x444444444444444444444444);
}

test "bigint sub equal" {
    var a = try BigInt.initSet(al, 0xefefefefefefefefefefefef);
    var b = try BigInt.initSet(al, 0xefefefefefefefefefefefef);

    var c = try BigInt.init(al);
    try c.sub(&a, &b);

    debug.assert((try c.to(u32)) == 0);
}

test "bigint mul single-single" {
    var a = try BigInt.initSet(al, 50);
    var b = try BigInt.initSet(al, 5);

    var c = try BigInt.init(al);
    try c.mul(&a, &b);

    debug.assert((try c.to(u64)) == 250);
}

test "bigint mul multi-single" {
    var a = try BigInt.initSet(al, 0xffffffff);
    var b = try BigInt.initSet(al, 2);

    var c = try BigInt.init(al);
    try c.mul(&a, &b);

    debug.assert((try c.to(u64)) == 0x1fffffffe);
}

test "bigint mul multi-multi" {
    var a = try BigInt.initSet(al, 0xefefefefefefefef);
    var b = try BigInt.initSet(al, 0xabababababababab);

    var c = try BigInt.init(al);
    try c.mul(&a, &b);

    debug.assert((try c.to(u128)) == 0xa0e62b70b5fb40848943feb9742ee9a5);
}

test "bigint mul alias r with a" {
    var a = try BigInt.initSet(al, 0xffffffff);
    var b = try BigInt.initSet(al, 2);

    try a.mul(&a, &b);

    debug.assert((try a.to(u64)) == 0x1fffffffe);
}

test "bigint mul alias r with b" {
    var a = try BigInt.initSet(al, 0xffffffff);
    var b = try BigInt.initSet(al, 2);

    try a.mul(&b, &a);

    debug.assert((try a.to(u64)) == 0x1fffffffe);
}

test "bigint mul alias r with a and b" {
    var a = try BigInt.initSet(al, 0xffffffff);

    try a.mul(&a, &a);

    debug.assert((try a.to(u128)) == 0xfffffffe00000001);
}

test "bigint mul a*0" {
    var a = try BigInt.initSet(al, 0xefefefefefefefef);
    var b = try BigInt.initSet(al, 0);

    var c = try BigInt.init(al);
    try c.mul(&a, &b);

    debug.assert((try c.to(u32)) == 0);
}

test "bigint mul 0*0" {
    var a = try BigInt.initSet(al, 0);
    var b = try BigInt.initSet(al, 0);

    var c = try BigInt.init(al);
    try c.mul(&a, &b);

    debug.assert((try c.to(u32)) == 0);
}

test "bigint div single-single no rem" {
    var a = try BigInt.initSet(al, 50);
    var b = try BigInt.initSet(al, 5);

    var q = try BigInt.init(al);
    var r = try BigInt.init(al);
    try BigInt.div(&q, &r, &a, &b);

    debug.assert((try q.to(u32)) == 10);
    debug.assert((try r.to(u32)) == 0);
}

test "bigint div single-single with rem" {
    var a = try BigInt.initSet(al, 49);
    var b = try BigInt.initSet(al, 5);

    var q = try BigInt.init(al);
    var r = try BigInt.init(al);
    try BigInt.div(&q, &r, &a, &b);

    debug.assert((try q.to(u32)) == 9);
    debug.assert((try r.to(u32)) == 4);
}

test "bigint div multi-single no rem" {
    var a = try BigInt.initSet(al, 0xffffeeeeddddcccc);
    var b = try BigInt.initSet(al, 34);

    var q = try BigInt.init(al);
    var r = try BigInt.init(al);
    try BigInt.div(&q, &r, &a, &b);

    debug.assert((try q.to(u64)) == 0x787870706868606);
    debug.assert((try r.to(u64)) == 0);
}

test "bigint div multi-single with rem" {
    var a = try BigInt.initSet(al, 0xffffeeeeddddcccf);
    var b = try BigInt.initSet(al, 34);

    var q = try BigInt.init(al);
    var r = try BigInt.init(al);
    try BigInt.div(&q, &r, &a, &b);

    debug.assert((try q.to(u64)) == 0x787870706868606);
    debug.assert((try r.to(u64)) == 3);
}

test "bigint div multi>2-single" {
    var a = try BigInt.initSet(al, 0xfefefefefefefefefefefefefefefefe);
    var b = try BigInt.initSet(al, 0xefab8);

    var q = try BigInt.init(al);
    var r = try BigInt.init(al);
    try BigInt.div(&q, &r, &a, &b);

    debug.assert((try q.to(u128)) == 0x1105ed38411293cea3e33c3498da);
    debug.assert((try r.to(u32)) == 0x3e4e);
}

test "bigint div single-single q < r" {
    var a = try BigInt.initSet(al, 0x0078f432);
    var b = try BigInt.initSet(al, 0x01000000);

    var q = try BigInt.init(al);
    var r = try BigInt.init(al);
    try BigInt.div(&q, &r, &a, &b);

    debug.assert((try q.to(u64)) == 0);
    debug.assert((try r.to(u64)) == 0x0078f432);
}

test "bigint div single-single q == r" {
    var a = try BigInt.initSet(al, 10);
    var b = try BigInt.initSet(al, 10);

    var q = try BigInt.init(al);
    var r = try BigInt.init(al);
    try BigInt.div(&q, &r, &a, &b);

    debug.assert((try q.to(u64)) == 1);
    debug.assert((try r.to(u64)) == 0);
}

test "bigint div q=0 alias" {
    var a = try BigInt.initSet(al, 3);
    var b = try BigInt.initSet(al, 10);

    try BigInt.div(&a, &b, &a, &b);

    debug.assert((try a.to(u64)) == 0);
    debug.assert((try b.to(u64)) == 3);
}

test "bigint div multi-multi q < r" {
    var a = try BigInt.initSet(al, 0xffffffff0078f432);
    var b = try BigInt.initSet(al, 0xffffffff01000000);

    var q = try BigInt.init(al);
    var r = try BigInt.init(al);
    try BigInt.div(&q, &r, &a, &b);

    debug.assert((try q.to(u64)) == 0);
    debug.assert((try r.to(u64)) == 0xffffffff0078f432);
}

// TODO: what behaviour/sign?
//test "bigint div single-single -/+" {
//    var a = try BigInt.initSet(al, -49);
//    var b = try BigInt.initSet(al, 5);
//
//    var q = try BigInt.init(al);
//    var r = try BigInt.init(al);
//    try BigInt.div(&q, &r, &a, &b);
//
//    debug.assert((try q.to(i32)) == -10);
//    debug.assert((try r.to(i32)) == 1);
//}
//
//test "bigint div single-single +/-" {
//    var a = try BigInt.initSet(al, 49);
//    var b = try BigInt.initSet(al, -5);
//
//    var q = try BigInt.init(al);
//    var r = try BigInt.init(al);
//    try BigInt.div(&q, &r, &a, &b);
//
//    debug.assert((try q.to(i32)) == -10);
//    debug.assert((try r.to(i32)) == -1);
//}
//
//test "bigint div single-single -/-" {
//    var a = try BigInt.initSet(al, -49);
//    var b = try BigInt.initSet(al, -5);
//
//    var q = try BigInt.init(al);
//    var r = try BigInt.init(al);
//    try BigInt.div(&q, &r, &a, &b);
//
//    debug.assert((try q.to(i32)) == 10);
//    debug.assert((try r.to(i32)) == -4);
//}
//
//test "bigint div multi-multi no rem" {
//    var a = try BigInt.initSet(al, 0xffffeeeeddddccccbbbbaaaa9999);
//    var b = try BigInt.initSet(al, 0x8888777766665555);
//
//    var q = try BigInt.init(al);
//    var r = try BigInt.init(al);
//    try BigInt.div(&q, &r, &a, &b);
//
//    debug.assert((try q.to(u64)) == 0x1e001c001f80);
//    debug.assert((try r.to(u64)) == 0x12e6f94cc72aa419);
//}
//
//test "bigint div multi-mutli with rem" {
//    var a = try BigInt.initSet(al, 0xffffeeeeddddb9e5c26ee37ff580);
//    var b = try BigInt.initSet(al, 0x8888777766665555);
//
//    var q = try BigInt.init(al);
//    var r = try BigInt.init(al);
//    try BigInt.div(&q, &r, &a, &b);
//
//    debug.assert((try q.to(u64)) == 0x1e001c001f80);
//    debug.assert((try r.to(u64)) == 0);
//}

test "bigint shift-right single" {
    var a = try BigInt.initSet(al, 0xffff0000);
    try a.shiftRight(a, 16);

    debug.assert((try a.to(u32)) == 0xffff);
}

test "bigint shift-right multi" {
    var a = try BigInt.initSet(al, 0xffff0000eeee1111dddd2222cccc3333);
    try a.shiftRight(a, 67);

    debug.assert((try a.to(u64)) == 0x1fffe0001dddc222);
}

test "bigint shift-left single" {
    var a = try BigInt.initSet(al, 0xffff);
    try a.shiftLeft(a, 16);

    debug.assert((try a.to(u64)) == 0xffff0000);
}

test "bigint shift-left multi" {
    var a = try BigInt.initSet(al, 0x1fffe0001dddc222);
    try a.shiftLeft(a, 67);

    debug.assert((try a.to(u128)) == 0xffff0000eeee11100000000000000000);
}

test "bigint bitwise and simple" {
    var a = try BigInt.initSet(al, 0xffffffff11111111);
    var b = try BigInt.initSet(al, 0xeeeeeeee22222222);

    try a.bitAnd(&a, &b);

    debug.assert((try a.to(u64)) == 0xeeeeeeee00000000);
}

test "bigint bitwise xor simple" {
    var a = try BigInt.initSet(al, 0xffffffff11111111);
    var b = try BigInt.initSet(al, 0xeeeeeeee22222222);

    try a.bitXor(&a, &b);

    debug.assert((try a.to(u64)) == 0x1111111133333333);
}

test "bigint bitwise or simple" {
    var a = try BigInt.initSet(al, 0xffffffff11111111);
    var b = try BigInt.initSet(al, 0xeeeeeeee22222222);

    try a.bitOr(&a, &b);

    debug.assert((try a.to(u64)) == 0xffffffff33333333);
}

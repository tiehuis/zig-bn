const std = @import("std");
const builtin = @import("builtin");
const debug = std.debug;
const math = std.math;
const mem = std.mem;
const Allocator = mem.Allocator;
const ArrayList = std.ArrayList;

const TypeId = builtin.TypeId;

const Limb = usize;
const DoubleLimb = @IntType(false, 2 * Limb.bit_count);
const Log2Limb = math.Log2Int(Limb);

pub const BigInt = struct {
    allocator: &Allocator,
    positive: bool,
    //  - little-endian ordered
    //  - len >= 1 always
    //  - zero value -> len == 1 with limbs[0] == 0
    limbs: []Limb,
    len: usize,

    pub fn init(allocator: &Allocator) !BigInt {
        return try BigInt.initCapacity(allocator, 4);
    }

    pub fn initSet(allocator: &Allocator, value: var) !BigInt {
        var s = try BigInt.init(allocator);
        try s.set(value);
        return s;
    }

    pub fn initCapacity(allocator: &Allocator, capacity: usize) !BigInt {
        return BigInt {
            .allocator = allocator,
            .positive = false,
            .limbs = block: {
                var limbs = try allocator.alloc(Limb, capacity);
                limbs[0] = 0;
                break :block limbs;
            },
            .len = 1,
        };
    }

    pub fn ensureCapacity(self: &BigInt, capacity: usize) !void {
        if (capacity <= self.limbs.len) {
            return;
        }

        self.limbs = try self.allocator.realloc(Limb, self.limbs, capacity);
    }

    pub fn deinit(self: &const BigInt) void {
        self.allocator.free(self.limbs);
    }

    pub fn clone(other: &const BigInt) !BigInt {
        return BigInt {
            .allocator = other.allocator,
            .positive = other.positive,
            .limbs = block: {
                var limbs = try other.allocator.alloc(Limb, other.len);
                mem.copy(Limb, limbs[0..], other.limbs[0..other.len]);
                break :block limbs;
            },
            .len = other.len,
        };
    }

    pub fn copy(self: &BigInt, other: &const BigInt) !void {
        if (self == other) {
            return;
        }

        self.positive = other.positive;
        try self.ensureCapacity(other.len);
        mem.copy(Limb, self.limbs[0..], other.limbs[0..other.len]);
        self.len = other.len;
    }

    pub fn swap(self: &BigInt, other: &BigInt) void {
        mem.swap(BigInt, self, other);
    }

    pub fn dump(self: &const BigInt) void {
        for (self.limbs) |limb| {
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

    fn bitcount(self: &const BigInt) usize {
        const u_bit_count = (self.len - 1) * Limb.bit_count + (Limb.bit_count - @clz(self.limbs[self.len - 1]));
        return usize(!self.positive) + u_bit_count;
    }

    pub fn sizeInBase(self: &const BigInt, base: usize) usize {
        return (self.bitcount() / math.log2(base)) + 1;
    }

    pub fn set(self: &BigInt, value: var) Allocator.Error!void {
        const T = @typeOf(value);

        switch (@typeInfo(T)) {
            TypeId.Int => |info| {
                try self.ensureCapacity(@sizeOf(T) / @sizeOf(Limb));
                self.positive = value >= 0;
                self.len = 0;

                var w_value = if (value < 0) -value else value;

                if (info.bits <= Limb.bit_count) {
                    self.limbs[0] = Limb(w_value);
                    self.len = 1;
                } else {
                    while (w_value != 0) |i| {
                        self.limbs[i] = @truncate(Limb, w_value);
                        self.len += 1;

                        // TODO: shift == 64 at compile-time fails. Need to fix.
                        w_value >>= Limb.bit_count / 2;
                        w_value >>= Limb.bit_count / 2;
                    }
                }
            },
            TypeId.IntLiteral => {
                var ilimbs = ArrayList(Limb).init(self.allocator);
                defer ilimbs.deinit();

                self.positive = value >= 0;
                self.len = 0;

                comptime var w_value = if (value < 0) -value else value;

                if (w_value <= @maxValue(Limb)) {
                    try ilimbs.append(w_value);
                } else {
                    const mask = (1 << Limb.bit_count) - 1;
                    inline while (w_value != 0) {
                        try ilimbs.append(w_value & mask);
                        w_value >>= Limb.bit_count / 2;
                        w_value >>= Limb.bit_count / 2;
                    }
                }

                try self.ensureCapacity(ilimbs.len);
                mem.copy(Limb, self.limbs, ilimbs.toSliceConst());
                self.len = ilimbs.len;
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
                if (self.bitcount() > 8 * @sizeOf(T)) {
                    return error.TargetTooSmall;
                }

                var r: T = 0;

                if (@sizeOf(T) <= @sizeOf(Limb)) {
                    r = T(self.limbs[0]);
                } else {
                    for (self.limbs[0..self.len]) |_, ri| {
                        const limb = self.limbs[self.len - ri - 1];
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

        var buffer: [128]u8 = undefined;
        var stack = std.heap.FixedBufferAllocator.init(buffer[0..]);
        var b = try BigInt.initSet(&stack.allocator, base);
        var p = try BigInt.init(&stack.allocator);

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
        // Non power-of-two: batch divisions per word size.
        else {
            const digits_per_limb = math.log(Limb, base, @maxValue(Limb));
            var limb_base: Limb = 1;
            var j: usize = 0;
            while (j < digits_per_limb) : (j += 1) {
                limb_base *= base;
            }

            var q = try self.clone();
            q.positive = true;
            var r = try BigInt.init(allocator);
            var b = try BigInt.initSet(allocator, limb_base);

            while (q.len >= 2) {
                try BigInt.divTrunc(&q, &r, &q, &b);

                var r_word = r.limbs[0];
                var i: usize = 0;
                while (i < digits_per_limb) : (i += 1) {
                    const ch = try digitToChar(u8(r_word % base), base);
                    r_word /= base;
                    try digits.append(ch);
                }
            }

            {
                std.debug.assert(q.len == 1);

                var r_word = q.limbs[0];
                while (r_word != 0) {
                    const ch = try digitToChar(u8(r_word % base), base);
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

    // returns -1, 0, 1 if |a| < |b|, |a| == |b| or |a| > |b| respectively.
    pub fn cmpAbs(a: &const BigInt, b: &const BigInt) i8 {
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
        return a.len == 1 and a.limbs[0] == 0;
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
    // [1, 2, 3, 4, 5] -> [1, 2, 3, 4, 5]
    // [0]             -> [0]
    fn norm1(r: &BigInt, length: usize) void {
        std.debug.assert(length > 0);

        if (r.limbs[length - 1] == 0) {
            std.debug.assert(length == 1 or r.limbs[length - 2] != 0);
            r.len = length - 1;
        } else {
            r.len = length;
        }
    }

    // Normalize a possible sequence of leading zeros.
    //
    // [1, 2, 3, 4, 0] -> [1, 2, 3, 4]
    // [1, 2, 0, 0, 0] -> [1, 2]
    // [0, 0, 0, 0, 0] -> [0]
    fn normN(r: &BigInt, length: usize) void {
        std.debug.assert(length > 0);
        std.debug.assert(length <= r.limbs.len);

        var j = length;
        while (j > 0) : (j -= 1) {
            if (r.limbs[j - 1] != 0) {
                break;
            }
        }

        // Handle zero
        r.len = if (j != 0) j else 1;
    }

    // r = a + b
    pub fn add(r: &BigInt, a: &const BigInt, b: &const BigInt) Allocator.Error!void {
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
                const bp = BigInt {
                    .allocator = undefined,
                    .positive = true,
                    .limbs = b.limbs,
                    .len = b.len,
                };
                try r.sub(a, bp);
            } else {
                // (-a) + (b) => b - a
                const ap = BigInt {
                    .allocator = undefined,
                    .positive = true,
                    .limbs = a.limbs,
                    .len = a.len,
                };
                try r.sub(b, ap);
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
                const bp = BigInt {
                    .allocator = undefined,
                    .positive = true,
                    .limbs = b.limbs,
                    .len = b.len,
                };
                try r.add(a, bp);
            } else {
                // (-a) - (b) => -(a + b)
                const ap = BigInt {
                    .allocator = undefined,
                    .positive = true,
                    .limbs = a.limbs,
                    .len = a.len,
                };
                try r.add(ap, b);
                r.positive = false;
            }
        } else {
            if (a.cmp(b) >= 0) {
                try r.ensureCapacity(a.len + 1);
                llsub(r.limbs[0..], a.limbs[0..a.len], b.limbs[0..b.len]);
                r.normN(a.len);
            } else {
                try r.ensureCapacity(b.len + 1);
                llsub(r.limbs[0..], b.limbs[0..b.len], a.limbs[0..a.len]);
                r.normN(b.len);
            }

            r.positive = a.positive;
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
            sr = try BigInt.initCapacity(rma.allocator, a.len + b.len);
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

    pub fn divFloor(q: &BigInt, r: &BigInt, a: &const BigInt, b: &const BigInt) !void {
        try div(q, r, a, b);

        // Trunc -> Floor.
        if (!q.positive) {
            var buffer: [128]u8 = undefined;
            var stack = std.heap.FixedBufferAllocator.init(buffer[0..]);
            var one = try BigInt.initSet(&stack.allocator, 1);

            try q.sub(q, &one);
            try r.add(q, &one);
        }
        r.positive = b.positive;
    }

    pub fn divTrunc(q: &BigInt, r: &BigInt, a: &const BigInt, b: &const BigInt) !void {
        try div(q, r, a, b);
        r.positive = a.positive;
    }

    // Truncates by default.
    fn div(quo: &BigInt, rem: &BigInt, a: &const BigInt, b: &const BigInt) !void {
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
            try quo.ensureCapacity(a.len + 2);
            try divN(quo.allocator, quo, rem, &x, &y);

            quo.positive = a.positive == b.positive;
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
                quo[i] = @truncate(Limb, @divTrunc(pdiv, b));
                *rem = @truncate(Limb, pdiv - (quo[i] *% b));
            }
        }
    }

    // Handbook of Applied Cryptography, 14.20
    //
    // x = qy + r where 0 <= r < y
    fn divN(allocator: &Allocator, q: &BigInt, r: &BigInt, x: &BigInt, y: &BigInt) !void {
        std.debug.assert(q.limbs.len >= x.len + 1);
        std.debug.assert(x.len >= y.len);

        const b = 1 << Limb.bit_count;

        var tmp = try BigInt.init(allocator);
        defer tmp.deinit();

        // minimum bounds for step 3.2
        try tmp.ensureCapacity(3);
        try r.ensureCapacity(3);

        // Normalize so y > b/2 (i.e. leading bit is set)
        const norm_shift = @clz(y.limbs[y.len - 1]);
        try x.shiftLeft(x, norm_shift);
        try y.shiftLeft(y, norm_shift);

        const n = x.len - 1;
        const t = y.len - 1;

        // 1.
        q.len = x.len + 1;
        mem.set(Limb, q.limbs[0..q.len], 0);

        // 2.
        try tmp.shiftLeft(y, Limb.bit_count * (n - t));
        while (x.cmp(&tmp) >= 0) {
            q.limbs[n-t] += 1;
            try x.sub(x, tmp);
        }

        // 3.
        var i = n;
        while (i > t) : (i -= 1) {
            // 3.1
            if (x.limbs[i] == y.limbs[t]) {
                q.limbs[i-t-1] = b - 1;
            } else {
                const num = DoubleLimb(x.limbs[i]) * b + DoubleLimb(x.limbs[i-1]);
                q.limbs[i-t-1] = Limb(@divTrunc(num, DoubleLimb(y.limbs[t])));
            }

            // 3.2
            //
            // We use r as a temporary since it is unused otherwise.
            tmp.limbs[0] = if (t >= 2) x.limbs[t-2] else 0;
            tmp.limbs[1] = if (t >= 1) x.limbs[t-1] else 0;
            tmp.limbs[2] = x.limbs[t];
            tmp.normN(3);

            while (true) {
                // 2x1 limb multiplication unrolled against single-limb q[i-t-1]
                var carry: Limb = 0;
                r.limbs[0] = addMulLimbWithCarry(0, if (t >= 1) y.limbs[t-1] else 0, q.limbs[i-t-1], &carry);
                r.limbs[1] = addMulLimbWithCarry(carry, y.limbs[t], q.limbs[i-t-1], &carry);
                r.limbs[2] = carry;
                r.normN(3);

                if (r.cmp(&tmp) <= 0) {
                    break;
                }

                q.limbs[i-t-1] -= 1;
            }

            // 3.3
            try tmp.set(q.limbs[i-t-1]);
            try tmp.mul(&tmp, y);
            try tmp.shiftLeft(&tmp, Limb.bit_count * (i - t - 1));
            try x.sub(x, &tmp);

            if (!x.positive) {
                try tmp.shiftLeft(y, Limb.bit_count * (i - t - 1));
                try x.add(x, &tmp);
                q.limbs[i-t-1] -= 1;
            }
        }

        // Denormalize
        q.normN(q.len);

        try r.shiftRight(x, norm_shift);
        r.normN(r.len);
    }

    // r = a << shift, in other words, r = a * 2^shift
    // TODO: We may want twos-complement shifting here.
    pub fn shiftLeft(r: &BigInt, a: &const BigInt, shift: usize) !void {
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
    // TODO: We may want twos-complement shifting here.
    pub fn shiftRight(r: &BigInt, a: &const BigInt, shift: usize) !void {
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
    pub fn bitAnd(r: &BigInt, a: &const BigInt, b: &const BigInt) !void {
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
    pub fn bitXor(r: &BigInt, a: &const BigInt, b: &const BigInt) !void {
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

const u256 = @IntType(false, 256);
var al = debug.global_allocator;

test "bigint comptime_int set" {
    comptime var s = 0xefffffff00000001eeeeeeefaaaaaaab;
    var a = try BigInt.initSet(al, s);

    const s_limb_count = 128 / Limb.bit_count;

    comptime var i: usize = 0;
    inline while (i < s_limb_count) : (i += 1) {
        const result = Limb(s & @maxValue(Limb));
        s >>= Limb.bit_count / 2;
        s >>= Limb.bit_count / 2;
        debug.assert(a.limbs[i] == result);
    }
}

test "bigint comptime_int set negative" {
    var a = try BigInt.initSet(al, -10);

    debug.assert(a.limbs[0] == 10);
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

test "bigint bitcount + sizeInBase" {
    var a = try BigInt.init(al);

    try a.set(0b100);
    debug.assert(a.bitcount() == 3);
    debug.assert(a.sizeInBase(2) >= 3);
    debug.assert(a.sizeInBase(10) >= 1);

    try a.set(0xffffffff);
    debug.assert(a.bitcount() == 32);
    debug.assert(a.sizeInBase(2) >= 32);
    debug.assert(a.sizeInBase(10) >= 10);

    try a.shiftLeft(&a, 5000);
    debug.assert(a.bitcount() == 5032);
    debug.assert(a.sizeInBase(2) >= 5032);
    a.positive = false;

    debug.assert(a.bitcount() == 5033);
    debug.assert(a.sizeInBase(2) >= 5033);
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
    var a = try BigInt.initSet(al, -0x7777777799999999ffffeeeeffffeeeeffffeeeef);
    var b = try BigInt.initSet(al, 0x7777777799999999ffffeeeeffffeeeeffffeeeee);

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
    var a = try BigInt.initSet(al, @maxValue(Limb));
    var b = try BigInt.initSet(al, 1);

    var c = try BigInt.init(al);
    try c.add(&a, &b);

    debug.assert((try c.to(u128)) == @maxValue(Limb) + 1);
}

test "bigint add multi-multi" {
    const op1 = 0xefefefef7f7f7f7f;
    const op2 = 0xfefefefe9f9f9f9f;
    var a = try BigInt.initSet(al, op1);
    var b = try BigInt.initSet(al, op2);

    var c = try BigInt.init(al);
    try c.add(&a, &b);

    debug.assert((try c.to(u128)) == op1 + op2);
}

test "bigint add zero-zero" {
    var a = try BigInt.initSet(al, 0);
    var b = try BigInt.initSet(al, 0);

    var c = try BigInt.init(al);
    try c.add(&a, &b);

    debug.assert((try c.to(u32)) == 0);
}

test "bigint add alias multi-limb nonzero-zero" {
    const op1 = 0xffffffff777777771;
    var a = try BigInt.initSet(al, op1);
    var b = try BigInt.initSet(al, 0);

    try a.add(&a, &b);

    debug.assert((try a.to(u128)) == op1);
}

test "bigint sub single-single" {
    var a = try BigInt.initSet(al, 50);
    var b = try BigInt.initSet(al, 5);

    var c = try BigInt.init(al);
    try c.sub(&a, &b);

    debug.assert((try c.to(u32)) == 45);
}

test "bigint sub multi-single" {
    var a = try BigInt.initSet(al, @maxValue(Limb) + 1);
    var b = try BigInt.initSet(al, 1);

    var c = try BigInt.init(al);
    try c.sub(&a, &b);

    debug.assert((try c.to(u64)) == @maxValue(Limb));
}

test "bigint sub multi-multi" {
    const op1 = 0xefefefefefefefefefefefef;
    const op2 = 0xabababababababababababab;

    var a = try BigInt.initSet(al, op1);
    var b = try BigInt.initSet(al, op2);

    var c = try BigInt.init(al);
    try c.sub(&a, &b);

    debug.assert((try c.to(u128)) == op1 - op2);
}

test "bigint sub equal" {
    var a = try BigInt.initSet(al, 0x11efefefefefefefefefefefef);
    var b = try BigInt.initSet(al, 0x11efefefefefefefefefefefef);

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
    var a = try BigInt.initSet(al, @maxValue(Limb));
    var b = try BigInt.initSet(al, 2);

    var c = try BigInt.init(al);
    try c.mul(&a, &b);

    debug.assert((try c.to(u128)) == 2 * @maxValue(Limb));
}

test "bigint mul multi-multi" {
    const op1 = 0x998888efefefefefefefef;
    const op2 = 0x333000abababababababab;
    var a = try BigInt.initSet(al, op1);
    var b = try BigInt.initSet(al, op2);

    var c = try BigInt.init(al);
    try c.mul(&a, &b);

    debug.assert((try c.to(u256)) == op1 * op2);
}

test "bigint mul alias r with a" {
    var a = try BigInt.initSet(al, @maxValue(Limb));
    var b = try BigInt.initSet(al, 2);

    try a.mul(&a, &b);

    debug.assert((try a.to(u128)) == 2 * @maxValue(Limb));
}

test "bigint mul alias r with b" {
    var a = try BigInt.initSet(al, @maxValue(Limb));
    var b = try BigInt.initSet(al, 2);

    try a.mul(&b, &a);

    debug.assert((try a.to(u128)) == 2 * @maxValue(Limb));
}

test "bigint mul alias r with a and b" {
    var a = try BigInt.initSet(al, @maxValue(Limb));

    try a.mul(&a, &a);

    debug.assert((try a.to(u128)) == @maxValue(Limb) * @maxValue(Limb));
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
    try BigInt.divTrunc(&q, &r, &a, &b);

    debug.assert((try q.to(u32)) == 10);
    debug.assert((try r.to(u32)) == 0);
}

test "bigint div single-single with rem" {
    var a = try BigInt.initSet(al, 49);
    var b = try BigInt.initSet(al, 5);

    var q = try BigInt.init(al);
    var r = try BigInt.init(al);
    try BigInt.divTrunc(&q, &r, &a, &b);

    debug.assert((try q.to(u32)) == 9);
    debug.assert((try r.to(u32)) == 4);
}

test "bigint div multi-single no rem" {
    const op1 = 0xffffeeeeddddcccc;
    const op2 = 34;

    var a = try BigInt.initSet(al, op1);
    var b = try BigInt.initSet(al, op2);

    var q = try BigInt.init(al);
    var r = try BigInt.init(al);
    try BigInt.divTrunc(&q, &r, &a, &b);

    debug.assert((try q.to(u64)) == op1 / op2);
    debug.assert((try r.to(u64)) == 0);
}

test "bigint div multi-single with rem" {
    const op1 = 0xffffeeeeddddcccf;
    const op2 = 34;

    var a = try BigInt.initSet(al, op1);
    var b = try BigInt.initSet(al, op2);

    var q = try BigInt.init(al);
    var r = try BigInt.init(al);
    try BigInt.divTrunc(&q, &r, &a, &b);

    debug.assert((try q.to(u64)) == op1 / op2);
    debug.assert((try r.to(u64)) == 3);
}

test "bigint div multi>2-single" {
    const op1 = 0xfefefefefefefefefefefefefefefefe;
    const op2 = 0xefab8;

    var a = try BigInt.initSet(al, op1);
    var b = try BigInt.initSet(al, op2);

    var q = try BigInt.init(al);
    var r = try BigInt.init(al);
    try BigInt.divTrunc(&q, &r, &a, &b);

    debug.assert((try q.to(u128)) == op1 / op2);
    debug.assert((try r.to(u32)) == 0x3e4e);
}

test "bigint div single-single q < r" {
    var a = try BigInt.initSet(al, 0x0078f432);
    var b = try BigInt.initSet(al, 0x01000000);

    var q = try BigInt.init(al);
    var r = try BigInt.init(al);
    try BigInt.divTrunc(&q, &r, &a, &b);

    debug.assert((try q.to(u64)) == 0);
    debug.assert((try r.to(u64)) == 0x0078f432);
}

test "bigint div single-single q == r" {
    var a = try BigInt.initSet(al, 10);
    var b = try BigInt.initSet(al, 10);

    var q = try BigInt.init(al);
    var r = try BigInt.init(al);
    try BigInt.divTrunc(&q, &r, &a, &b);

    debug.assert((try q.to(u64)) == 1);
    debug.assert((try r.to(u64)) == 0);
}

test "bigint div q=0 alias" {
    var a = try BigInt.initSet(al, 3);
    var b = try BigInt.initSet(al, 10);

    try BigInt.divTrunc(&a, &b, &a, &b);

    debug.assert((try a.to(u64)) == 0);
    debug.assert((try b.to(u64)) == 3);
}

test "bigint div multi-multi q < r" {
    const op1 = 0x1ffffffff0078f432;
    const op2 = 0x1ffffffff01000000;
    var a = try BigInt.initSet(al, op1);
    var b = try BigInt.initSet(al, op2);

    var q = try BigInt.init(al);
    var r = try BigInt.init(al);
    try BigInt.divTrunc(&q, &r, &a, &b);

    debug.assert((try q.to(u128)) == 0);
    debug.assert((try r.to(u128)) == op1);
}

test "bigint div trunc single-single +/+" {
    const u: i32 = 5;
    const v: i32 = 3;

    var a = try BigInt.initSet(al, u);
    var b = try BigInt.initSet(al, v);

    var q = try BigInt.init(al);
    var r = try BigInt.init(al);
    try BigInt.divTrunc(&q, &r, &a, &b);

    // n = q * d + r
    // 5 = 1 * 3 + 2
    const eq = @divTrunc(u, v);
    const er = @mod(u, v);

    debug.assert((try q.to(i32)) == eq);
    debug.assert((try r.to(i32)) == er);
}

test "bigint div trunc single-single -/+" {
    const u: i32 = -5;
    const v: i32 = 3;

    var a = try BigInt.initSet(al, u);
    var b = try BigInt.initSet(al, v);

    var q = try BigInt.init(al);
    var r = try BigInt.init(al);
    try BigInt.divTrunc(&q, &r, &a, &b);

    //  n = q *  d + r
    // -5 = 1 * -3 - 2
    const eq = -1;
    const er = -2;

    debug.assert((try q.to(i32)) == eq);
    debug.assert((try r.to(i32)) == er);
}

test "bigint div trunc single-single +/-" {
    const u: i32 = 5;
    const v: i32 = -3;

    var a = try BigInt.initSet(al, u);
    var b = try BigInt.initSet(al, v);

    var q = try BigInt.init(al);
    var r = try BigInt.init(al);
    try BigInt.divTrunc(&q, &r, &a, &b);

    // n =  q *  d + r
    // 5 = -1 * -3 + 2
    const eq = -1;
    const er = 2;

    debug.assert((try q.to(i32)) == eq);
    debug.assert((try r.to(i32)) == er);
}

test "bigint div trunc single-single -/-" {
    const u: i32 = -5;
    const v: i32 = -3;

    var a = try BigInt.initSet(al, u);
    var b = try BigInt.initSet(al, v);

    var q = try BigInt.init(al);
    var r = try BigInt.init(al);
    try BigInt.divTrunc(&q, &r, &a, &b);

    //  n = q *  d + r
    // -5 = 1 * -3 - 2
    const eq = 1;
    const er = -2;

    debug.assert((try q.to(i32)) == eq);
    debug.assert((try r.to(i32)) == er);
}

test "bigint div floor single-single +/+" {
    const u: i32 = 5;
    const v: i32 = 3;

    var a = try BigInt.initSet(al, u);
    var b = try BigInt.initSet(al, v);

    var q = try BigInt.init(al);
    var r = try BigInt.init(al);
    try BigInt.divFloor(&q, &r, &a, &b);

    //  n =  q *  d + r
    //  5 =  1 *  3 + 2
    const eq = 1;
    const er = 2;

    debug.assert((try q.to(i32)) == eq);
    debug.assert((try r.to(i32)) == er);
}

test "bigint div floor single-single -/+" {
    const u: i32 = -5;
    const v: i32 = 3;

    var a = try BigInt.initSet(al, u);
    var b = try BigInt.initSet(al, v);

    var q = try BigInt.init(al);
    var r = try BigInt.init(al);
    try BigInt.divFloor(&q, &r, &a, &b);

    //  n =  q *  d + r
    // -5 = -2 *  3 + 1
    const eq = -2;
    const er = 1;

    debug.assert((try q.to(i32)) == eq);
    debug.assert((try r.to(i32)) == er);
}

test "bigint div floor single-single +/-" {
    const u: i32 = 5;
    const v: i32 = -3;

    var a = try BigInt.initSet(al, u);
    var b = try BigInt.initSet(al, v);

    var q = try BigInt.init(al);
    var r = try BigInt.init(al);
    try BigInt.divFloor(&q, &r, &a, &b);

    //  n =  q *  d + r
    //  5 = -2 * -3 - 1
    const eq = -2;
    const er = -1;

    debug.assert((try q.to(i32)) == eq);
    debug.assert((try r.to(i32)) == er);
}

test "bigint div floor single-single -/-" {
    const u: i32 = -5;
    const v: i32 = -3;

    var a = try BigInt.initSet(al, u);
    var b = try BigInt.initSet(al, v);

    var q = try BigInt.init(al);
    var r = try BigInt.init(al);
    try BigInt.divFloor(&q, &r, &a, &b);

    //  n =  q *  d + r
    // -5 =  2 * -3 + 1
    const eq = 1;
    const er = -2;

    debug.assert((try q.to(i32)) == eq);
    debug.assert((try r.to(i32)) == er);
}

test "bigint div multi-multi no rem" {
    var a = try BigInt.initSet(al, 0x8888999911110000ffffeeeeddddccccbbbbaaaa9999);
    var b = try BigInt.initSet(al, 0x99990000111122223333);

    var q = try BigInt.init(al);
    var r = try BigInt.init(al);
    try BigInt.divTrunc(&q, &r, &a, &b);

    debug.assert((try q.to(u128)) == 0xe38f38e39161aaabd03f0f1b);
    debug.assert((try r.to(u128)) == 0x28de0acacd806823638);
}

test "bigint div multi-mutli with rem" {
    var a = try BigInt.initSet(al, 0x8888999911110000ffffeeeedb4fec200ee3a4286361);
    var b = try BigInt.initSet(al, 0x99990000111122223333);

    var q = try BigInt.init(al);
    var r = try BigInt.init(al);
    try BigInt.divTrunc(&q, &r, &a, &b);

    debug.assert((try q.to(u128)) == 0xe38f38e39161aaabd03f0f1b);
    debug.assert((try r.to(u128)) == 0);
}

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

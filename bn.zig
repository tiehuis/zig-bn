const std = @import("std");
const builtin = @import("builtin");
const TypeId = builtin.TypeId;
const assert = std.debug.assert;
const printf = std.io.stdout.printf;

const ll = @import("ll.zig");
const Bn = BnWithAllocator(&std.debug.global_allocator);

// TODO: Use addWithOverflow and friends instead so we can use wider (64-bit) base types.
pub const Limb = u32;
pub const DoubleLimb = @IntType(false, 2 * 8 * @sizeOf(Limb));
pub const Limbs = std.ArrayList(Limb);
pub const Cmp = std.math.Cmp;

error InvalidBase;
error ParseError;
error InputTooShort;

/// Instantiate a new Bn factory with an underlying allocator.
///
/// The reason this is a factory-like function is to avoid the following:
///
/// ```
/// const Bn = @import("bn.zig").Bn;
///
/// var a = %%Bn.init(&global_allocator);
/// var b = %%Bn.init(&global_allocator);
/// var c = %%Bn.init(&global_allocator);
/// var d = %%Bn.init(&global_allocator);
/// ```
///
/// Since the number of allocators in use tends to be small, we can instead use it in the following
/// way.
///
/// ```
/// const bn = const @import("bn.zig");
/// const Bn = bn.BnWithAllocator(&global_allocator);
///
/// var a = %%Bn.init();
/// var b = %%Bn.init();
/// var c = %%Bn.init();
/// var d = %%Bn.init();
/// ```
pub fn BnWithAllocator(comptime allocator: &std.mem.Allocator) -> type { struct {
    const Self = this;

    limbs: Limbs,
    positive: bool,
    allocator: &std.mem.Allocator,

    /// Initialize a new Bn object.
    ///
    /// Every Bn object is zero-initialized by default and must allocate at least 1 limb of memory,
    /// hence this may fail.
    pub fn init() -> %Self {
        var limbs = Limbs.init(allocator);
        %return limbs.append(0);

        Self {
            .limbs = limbs,
            .positive = true,
            .allocator = allocator
        }
    }

    /// Release the storage associated with this Bn object.
    pub fn deinit(self: &Self) {
        self.limbs.deinit();
    }

    /// Try convert a Bn object to a smaller-width primitive type.
    ///
    /// Returns null if the Bn object cannot be converted to the specified type without loss.
    pub fn to(self: &Self, comptime T: type) -> ?T {
        if (@typeId(T) == TypeId.Int) {
            if (T.is_signed) {
                if (self.limbs.len == 1) {
                    const value = self.limbs.items[0];
                    // TODO: Check negative underflow possibility.
                    if (self.positive) T(value) else -T(value)
                } else {
                    null
                }
            } else {
                if (self.limbs.len == 1) {
                    T(self.limbs.items[0])
                } else {
                    null
                }
            }
        } else {
            @compileError("no `to` implementation for type");
        }
    }

    fn debugPrint(self: &Self) {
        for (self.limbs.toSliceConst()) |d| {
            %%printf("{} ", d);
        }
        %%printf("\n");
    }

    /// Clone a Bn object, creating a new instance initialized to the same value.
    pub fn clone(self: &Self) -> %Self {
        var limbs = Limbs.init(self.allocator);
        %return limbs.resize(self.limbs.len);

        for (self.limbs.toSliceConst()) |d, i| {
            limbs.items[i] = d;
        }

        Self {
            .limbs = limbs,
            .positive = self.positive,
            .allocator = self.allocator
        }
    }

    /// Copy the value of a Bn object to another.
    pub fn copy(self: &Self, other: &Self) -> %void {
        %return self.limbs.resize(other.limbs.len);
        for (other.limbs.toSliceConst()) |d, i| {
            self.limbs.items[i] = d;
        }
        self.positive = other.positive;
    }

    /// Set the value of a Bn object based on some primitive type.
    pub fn set(self: &Self, comptime T: type, value: T) -> %void {
        comptime assert(@typeId(T) == builtin.TypeId.Int);
        // TODO: Allow halving a multiple-sized types into sequence of limbs.
        comptime assert(@sizeOf(T) <= @sizeOf(Limb));

        %return self.limbs.resize(1);
        if (!T.is_signed) {
            self.limbs.items[0] = Limb(value);
            self.positive = true;
        } else {
            // TODO: Check negative underflow possibility.
            self.limbs.items[0] = Limb(%%std.math.absInt(value));
            self.positive = false;
        }
    }

    /// Set the value of a Bn object to zero.
    ///
    /// This does not reclaim any previously used memory.
    pub fn zero(self: &Self) {
        self.limbs.resizeDown(1);
        self.limbs.items[0] = 0;
    }

    // Zero-extend new allocation space in preparation for an operation.
    //
    // This will only modify the capacity and zero due to aliasing requirement.
    fn zeroExtend(self: &Self, n: usize) -> %void {
        %return self.limbs.ensureCapacity(n);
        var i = self.limbs.len;
        while (i <= n) : (i += 1) {
            self.limbs.items[i] = 0;
        }
    }

    // Reduce a Bn, removing any trailing zeroes.
    //
    // We work from the bottom for now to ensure that the length is set appropriately as
    // there are a number of places where we modify the buffer directly.
    fn reduce(self: &Self) {
        for (self.limbs.items) |d, i| {
            if (d == 0) {
                self.limbs.len = i;
                break;
            }
        }
    }

    // Converts a single character using the specified radix-map.
    fn convertFromBaseChar(value: u8, radix: u8) -> %u8 {
        const result = {
            if (value >= '0' and value <= '9') {
                value - '0'
            } else if (value >= 'A' and value <= 'Z') {
                value - 'A' + 10
            } else if (value >= 'a' and value <= 'z') {
                value - 'a' + 36
            } else {
                @maxValue(u8)
            }
        };

        if (result < radix) {
            result
        } else {
            error.ParseError
        }
    }

    // Converts to a single character using the specified radix.
    fn convertToBaseChar(value: u8, radix: u8) -> %u8 {
        assert(value < radix);
        const radixMap = "0123456789abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ";

        if (radix < 62) {
            radixMap[value]
        } else {
            error.ParseError
        }
    }

    /// Return the number of bits required to represent the Bn object.
    ///
    /// Negative values return the same count as their positive counterparts and do not attach an
    /// extra bit for the leading sign bit.
    pub fn bitLen(self: &Self) -> usize {
        assert(self.limbs.len > 0);
        const base_bits = 8 * @sizeOf(Limb) * (self.limbs.len - 1);
        base_bits + (8 * @sizeOf(Limb) - @clz(self.limbs.items[self.limbs.len - 1]))
    }

    /// Set the Bn its absolute value.
    pub fn abs(self: &Self) {
        self.positive = true;
    }

    /// Set the Bn to its negation.
    pub fn neg(self: &Self) {
        self.positive = !self.positive;
    }

    /// Return true if the Bn is equal to zero.
    pub fn isZero(self: &Self) -> bool {
        self.limbs.len == 1 and self.limbs.items[0] == 0
    }

    /// Return true if the Bn is equal to one.
    pub fn isOne(self: &Self) -> bool {
        self.limbs.len == 1 and self.limbs.items[0] == 1
    }

    /// Return the sign of the Bn.
    ///
    /// -1 => negative
    ///  0 => zero
    /// +1 => positive
    pub fn sign(self: &Self) -> isize {
        if (self.isZero()) {
            return 0;   // These return statements are required to avoid a compile error!
        } else if (self.positive) {
            return 1;
        } else {
            -1
        }
    }

    // Is there a builtin for this?
    fn popcnt(v: Limb) -> usize {
        var n: Limb = v;
        var sum: usize = 0;
        while (n != 0) : (n >>= 1) {
            sum += n & 1;
        }
        sum
    }

    /// Return the number of bits that are set in the Bn.
    pub fn popcount(self: &Self) -> usize {
        var pop: usize = 0;
        for (self.limbs.toSliceConst()) |b| {
            pop += popcnt(b);
        }
        pop
    }

    /// Set the big number to the value specified by the string.
    ///
    /// The input radix accepts values from the range [2, 62].
    /// Digits are used first, then upper-case letters and finally lower-case letters.
    ///
    /// If an error occurs no guarantees are made about the resulting state of the Bn.
    pub fn setStr(self: &Self, base: u8, value: []const u8) -> %void {
        if (value.len == 0) {
            return error.InputTooShort;
        }
        if (base < 2 or base > 62) {
            return error.InvalidBase;
        }

        const tail = {
            if (value[0] == '-') {
                self.positive = false;
                value[1..]
            }
            else if (value[0] == '+') {
                self.positive = true;
                value[1..]
            }
            else {
                self.positive = true;
                value
            }
        };

        if (tail.len == 0) {
            return error.InputTooShort;
        }

        const approxLength = ((std.math.log(2, base) * value.len) + 1) / (8 * @sizeOf(Limb)) + 1;
        %return self.zeroExtend(approxLength);
        self.zero();

        var mult = %return Bn.init();
        mult.zero();
        defer mult.deinit();

        var radix = %return Bn.init();
        %%radix.set(u8, base);
        defer radix.deinit();

        for (tail) |item, i| {
            %return mul(self, self, &radix);
            const d = %return convertFromBaseChar(item, base);
            %%mult.set(u8, d);
            %return add(self, self, &mult);
        }

        self.reduce();
    }

    /// Converts the big number to a string representation in the given radix.
    ///
    /// The string is allocated using the internal allocator.
    // TODO: Redo once corrected div behaviour.
    pub fn toStr(self: &Self, base: u8) -> %std.ArrayList(u8) {
        if (base < 2 or base > 62) {
            return error.InvalidBase;
        }

        var str = std.ArrayList(u8).init(self.allocator);

        if (self.isZero()) {
            %return str.append('0');
            return str;
        }

        var tmp = %return self.clone();
        tmp.positive = true;    // Handle negative separately.
        defer tmp.deinit();

        var r = %return Bn.init();
        defer r.deinit();
        var b = %return Bn.init();
        defer b.deinit();
        %%b.set(u8, base);

        var i: usize = 0;
        while (!tmp.isZero() and i < 10) : (i += 1) {
            if (cmp(&tmp, &b) == Cmp.Less) {
                const char = %return convertToBaseChar(??tmp.to(u8), base);
                %return str.append(char);
                break;
            } else {
                %return div(&tmp, &r, &tmp, &b);
                const char = %return convertToBaseChar(??r.to(u8), base);
                %return str.append(char);
            }
        }

        // Space for '-'
        if (!self.positive) {
            %return str.append('X');
        }

        const slice = str.toSlice();
        var j: usize = 0;
        while (j < slice.len / 2) : (j += 1) {
            const k = slice.len - j - 1;
            const t = slice[k];
            slice[k] = slice[j];
            slice[j] = t;
        }

        if (!self.positive) {
            str.items[0] = '-';
        }

        return str;
    }

    /// Return the comparision between two Bn values.
    ///
    /// -1 => a > b
    ///  0 => a == b
    /// +1 => a < b
    pub fn cmp(a: &Bn, b: &Bn) -> Cmp {
        if (a.positive and !b.positive) {
            return Cmp.Greater;
        } else if (b.positive and !a.positive) {
            return Cmp.Less;
        }

        var result = if (a.limbs.len < b.limbs.len) {
            Cmp.Less
        } else if (a.limbs.len > b.limbs.len) {
            Cmp.Greater
        } else {
            std.mem.cmp(Limb, a.limbs.toSliceConst(), b.limbs.toSliceConst())
        };

        if (a.positive and b.positive) {
            result
        } else {
            if (result == Cmp.Greater) {
                Cmp.Less
            } else if (result == Cmp.Less) {
                Cmp.Greater
            } else {
                Cmp.Equal
            }
        }
    }

    /// Compute the quotient (q) and remainder (r) of a / b.
    ///
    /// q = a / b + r
    // TODO: Only handles single limb division right now!
    pub fn div(q: &Bn, r: &Bn, a: &Bn, b: &Bn) -> %void {
        assert(!b.isZero());

        if (a.isZero()) {
            %%q.set(u8, 0);
            %%r.set(u8, 0);
            return;
        }
        if (b.isOne()) {
            %%q.copy(a);
            %%r.set(u8, 0);
        }

        // Note: lots of possible aliasing here so double-check. May need copies.
        %return q.zeroExtend(a.limbs.len);
        r.zero();   // Reduce to single limb

        ll.divRemSingle(q.limbs.items, &r.limbs.items[0], a.limbs.toSliceConst(), b.limbs.items[0]);
        q.reduce();
    }

    /// Compute the value of a + b.
    ///
    /// dst = a + b
    pub fn add(dst: &Bn, a: &Bn, b: &Bn) -> %void {
        if (a.positive != b.positive) {
            // (a) + (-b) => a - b
            if (a.positive) {
                b.abs();
                %return sub(dst, a, b);
                b.neg();
            }
            // (-a) + (b) => b - a
            else {
                a.abs();
                %return sub(dst, b, a);
                a.neg();
            }
        } else {
            if (a.limbs.len >= b.limbs.len) {
                // if dst aliases a then we cannot use the slice itself, nor can we do an actual resize.
                %return dst.zeroExtend(a.limbs.len + 1);
                ll.add3(dst.limbs.items, a.limbs.toSliceConst(), b.limbs.toSliceConst());
                dst.reduce();
            } else {
                %return dst.zeroExtend(b.limbs.len + 1);
                ll.add3(dst.limbs.items, b.limbs.toSliceConst(), a.limbs.toSliceConst());
                dst.reduce();
            }

            dst.positive = a.positive;
        }
    }

    /// Compute the value of a - b.
    ///
    /// dst = a - b
    pub fn sub(dst: &Bn, a: &Bn, b: &Bn) -> %void {
        const cr = a.cmp(b);
        if (cr == Cmp.Greater) {
            %return dst.zeroExtend(b.limbs.len);
            ll.sub3(dst.limbs.items, a.limbs.toSlice(), b.limbs.toSlice());
            dst.reduce();
            dst.positive = true;
        } else if (cr == Cmp.Less) {
            %return dst.zeroExtend(a.limbs.len);
            ll.sub3(dst.limbs.items, b.limbs.toSlice(), a.limbs.toSlice());
            dst.reduce();
            dst.positive = false;
        } else {
            // Limb size will never be smaller than u8.
            %%dst.set(u8, 0);
        }
    }

    /// Compute the value of a * b.
    ///
    /// dst = a * b
    pub fn mul(dst: &Bn, a: &Bn, b: &Bn) -> %void {
        const a_sign = a.positive;
        const b_sign = b.positive;
        const signn = a_sign == b_sign;
        a.positive = true;
        b.positive = true;

        // TODO: Don't copy if non-alias.
        var temp = Limbs.init(&std.debug.global_allocator);
        defer temp.deinit();
        %return temp.resize(a.limbs.len + b.limbs.len + 1);

        if (a.limbs.len >= b.limbs.len) {
            ll.muladd3(temp.items, a.limbs.toSliceConst(), b.limbs.toSliceConst());
        } else {
            ll.muladd3(temp.items, b.limbs.toSliceConst(), a.limbs.toSliceConst());
        }

        for (temp.items) |item, i| { dst.limbs.items[i] = item }
        dst.reduce();

        a.positive = a_sign;
        b.positive = b_sign;
        dst.positive = signn;
    }
}}

test "test_defaultZero" {
    var a = %%Bn.init();
    defer a.deinit();

    assert(a.limbs.items[0] == 0);
    assert(a.positive);
}

test "set" {
    var a = %%Bn.init();
    defer a.deinit();

    %%a.set(u8, 5);
    assert(a.limbs.items[0] == 5);
    assert(a.positive == true);

    %%a.set(u16, @maxValue(u16));
    assert(a.limbs.items[0] == @maxValue(u16));
    assert(a.positive == true);

    %%a.set(i32, -5);
    assert(a.limbs.items[0] == 5);
    assert(a.positive == false);
}

test "clone" {
    var a = %%Bn.init();
    defer a.deinit();

    %%a.set(u8, 5);
    var b = %%a.clone();
    defer b.deinit();
    assert(a.positive == b.positive);
    assert(??a.to(u8) == ??b.to(u8));

    %%a.set(i8, -5);
    var c = %%a.clone();
    assert(a.positive == c.positive);
    assert(??a.to(i8) == ??c.to(i8));
}

test "copy" {
    var a = %%Bn.init();
    defer a.deinit();

    var b = %%Bn.init();
    defer b.deinit();

    %%a.set(u8, 5);
    %%b.copy(&a);
    assert(a.positive == b.positive);
    assert(??a.to(u8) == ??b.to(u8));

    %%a.set(i8, -5);
    %%b.copy(&a);
    assert(a.positive == b.positive);
    assert(??a.to(i8) == ??b.to(i8));
}

test "toInt" {
    var a = %%Bn.init();
    defer a.deinit();
    assert(??a.to(i64) == 0);

    a.limbs.items[0] = 5;
    a.positive = true;
    assert(??a.to(u64) == 5);
    assert(??a.to(i64) == 5);

    a.limbs.items[0] = @maxValue(u16);
    a.positive = true;
    assert(??a.to(u64) == @maxValue(u16));

    a.limbs.items[0] = 5;
    a.positive = false;
    assert(??a.to(i64) == -5);
}

test "bitLen" {
    var a = %%Bn.init();
    defer a.deinit();

    %%a.set(u8, 0);
    assert(a.bitLen() == 0);

    %%a.set(u8, 1);
    assert(a.bitLen() == 1);

    %%a.set(u8, 0xFF);
    assert(a.bitLen() == 8);

    %%a.set(Limb, @maxValue(Limb));
    assert(a.bitLen() == 8 * @sizeOf(Limb));

    %%a.setStr(16, "1FFFFFFFF");
    assert(a.bitLen() == 33);
}

test "abs" {
    var a = %%Bn.init();
    defer a.deinit();

    %%a.set(u8, 0);
    a.abs();
    assert(??a.to(i64) == 0);

    %%a.set(u8, 1);
    a.abs();
    assert(??a.to(i64) == 1);

    %%a.set(i8, -1);
    a.abs();
    assert(??a.to(i64) == 1);
}

test "neg" {
    var a = %%Bn.init();
    defer a.deinit();

    %%a.set(u8, 0);
    a.neg();
    assert(??a.to(i64) == 0);

    %%a.set(u8, 1);
    a.neg();
    assert(??a.to(i64) == -1);

    %%a.set(i8, -1);
    a.neg();
    assert(??a.to(i64) == 1);
}

test "isZero" {
    var a = %%Bn.init();
    defer a.deinit();

    %%a.set(u8, 0);
    assert(a.isZero());

    %%a.set(u8, 1);
    assert(!a.isZero());
}

test "sign" {
    var a = %%Bn.init();
    defer a.deinit();

    %%a.set(u8, 0);
    assert(a.sign() == 0);

    %%a.set(u8, 234);
    assert(a.sign() == 1);

    %%a.set(i8, -23);
    assert(a.sign() == -1);
}

test "popcount" {
    var a = %%Bn.init();
    defer a.deinit();

    %%a.set(u8, 0);
    assert(a.popcount() == 0);

    %%a.set(u8, 1);
    assert(a.popcount() == 1);

    %%a.set(u16, 0x1FF);
    assert(a.popcount() == 9);

    %%a.setStr(16, "FFFFFFFF");
    assert(a.popcount() == 32);

    %%a.setStr(16, "2FFFFFFFF");
    assert(a.popcount() == 33);

    %%a.setStr(16, "3FFFFFFFF");
    assert(a.popcount() == 34);
}

test "setStr" {
    var a = %%Bn.init();
    defer a.deinit();

    %%a.setStr(10, "1");
    assert(??a.to(i64) == 1);

    %%a.setStr(10, "1238");
    assert(??a.to(i64) == 1238);

    %%a.setStr(10, "1230912412");
    assert(??a.to(i64) == 1230912412);

    %%a.setStr(16, "FFFFFFFF");
    assert(??a.to(u64) == @maxValue(u32));

    // TODO: Remove test assumption that on size of limb.
    %%a.setStr(16, "FFFFFFFFFF");
    assert(a.limbs.items[0] == @maxValue(Limb));
    assert(a.limbs.items[1] == 0xFF);

    %%a.setStr(16, "FFEEFFEFAABBAABACCDDCCDC");
    assert(a.limbs.items[0] == 0xCCDDCCDC);
    assert(a.limbs.items[1] == 0xAABBAABA);
    assert(a.limbs.items[2] == 0xFFEEFFEF);

    %%a.setStr(10, "240530240918");
    assert(a.limbs.items[0] == 12072342);
    assert(a.limbs.items[1] == 56);

    // Set negatives failing.
    //%%a.setStr(10, "-10");
    //assert(??a.to(i32) == -10);

    // TODO: Requires compiler support for equality against errors
    //var r = %%a.setStr("A123");
    //assert(r == error.ParseError);
}

test "toStr" {
    var a = %%Bn.init();
    defer a.deinit();

    a.zero();
    assert(std.mem.eql(u8, (%%a.toStr(10)).toSlice(), "0"));

    %%a.set(u8, 60);
    assert(std.mem.eql(u8, (%%a.toStr(10)).toSlice(), "60"));

    // TODO: Fix multi-limb case + negative handling.
    const in1 = "240530240";
    %%a.setStr(10, in1);
    assert(std.mem.eql(u8, (%%a.toStr(10)).toSlice(), in1));
}

test "cmp" {
    var a = %%Bn.init();
    defer a.deinit();

    var b = %%Bn.init();
    defer b.deinit();

    %%a.set(u8, 0);
    %%b.set(u8, 1);
    assert(Bn.cmp(&a, &b) == Cmp.Less);

    %%a.set(u8, 1);
    %%b.set(u8, 0);
    assert(Bn.cmp(&a, &b) == Cmp.Greater);

    %%a.set(u8, 1);
    %%b.set(u8, 1);
    assert(Bn.cmp(&a, &b) == Cmp.Equal);
}

test "subSimple" {
    var a = %%Bn.init();
    defer a.deinit();
    %%a.set(u32, 5);

    var b = %%Bn.init();
    defer b.deinit();
    %%b.set(u32, 5);

    var c = %%Bn.init();
    defer c.deinit();
    %%c.set(u32, 8);

    %%Bn.sub(&a, &c, &b);
    assert(??a.to(i64) == 3);

    %%Bn.sub(&a, &b, &c);
    assert(??a.to(i64) == -3);
}

test "addSingle" {
    var a = %%Bn.init();
    defer a.deinit();
    %%a.set(u32, 5);

    var b = %%Bn.init();
    defer b.deinit();
    %%b.set(u32, 7);

    var c = %%Bn.init();
    defer c.deinit();
    %%c.set(u32, 13);

    %%Bn.add(&a, &b, &c);
    assert(??a.to(u64) == 20);

    %%Bn.add(&a, &c, &b);
    assert(??a.to(u64) == 20);

    %%Bn.add(&a, &c, &c);
    assert(??a.to(u64) == 26);

    %%Bn.add(&a, &a, &a);
    assert(??a.to(u64) == 52);

    %%Bn.add(&a, &a, &b);
    assert(??a.to(u64) == 59);
}

test "addSingleNegative" {
    var a = %%Bn.init();
    defer a.deinit();
    %%a.set(u32, 5);

    var b = %%Bn.init();
    defer b.deinit();
    %%b.set(i32, -7);

    var c = %%Bn.init();
    defer c.deinit();
    %%c.set(u32, 13);

    %%Bn.add(&a, &b, &c);
    assert(??a.to(u64) == 6);

    %%Bn.add(&a, &c, &b);
    assert(??a.to(u64) == 6);

    %%b.set(i32, 14);
    %%c.set(i32, -14);
    %%Bn.add(&a, &b, &c);
    // TODO: Fix negative Bn.addition case.
    //assert(??a.to(i64) == 0);

    %%b.set(i32, -14);
    %%c.set(i32, 13);
    %%Bn.add(&a, &b, &c);
    //assert(??a.to(i64) == -1);

    %%Bn.add(&a, &c, &b);
    //assert(??a.to(i64) == -1);

    %%b.set(i32, -3);
    %%c.set(i32, -5);
    //assert(??a.to(i64) == -8);
}

test "addMulti" {
    var a = %%Bn.init();
    defer a.deinit();
    %%a.setStr(16, "FFFFFFFF");

    var b = %%Bn.init();
    defer b.deinit();
    %%b.setStr(16, "FFFFFFFF");

    var c = %%Bn.init();
    defer c.deinit();

    %%Bn.add(&c, &a, &b);
    // TODO: Implement toStr before assertions
}

test "mulSingle" {
    var a = %%Bn.init();
    defer a.deinit();

    var b = %%Bn.init();
    defer b.deinit();

    var c = %%Bn.init();
    defer c.deinit();

    %%a.set(i8, 5);
    %%b.set(i8, 5);
    %%Bn.mul(&a, &a, &b);
    assert(??a.to(u64) == 25);

    %%b.set(u8, 7);
    %%c.set(u8, 3);
    %%Bn.mul(&a, &b, &c);
    assert(??a.to(u64) == 21);

    %%b.set(u8, 90);
    %%c.set(u8, 78);
    %%Bn.mul(&a, &b, &c);
    assert(??a.to(u64) == 7020);

    %%b.set(i8, -90);
    %%c.set(u8, 78);
    %%Bn.mul(&a, &b, &c);
    assert(??a.to(i64) == -7020);

    %%b.set(u8, 90);
    %%c.set(i8, -78);
    %%Bn.mul(&a, &b, &c);
    assert(??a.to(i64) == -7020);

    %%b.set(i8, -90);
    %%c.set(i8, -78);
    %%Bn.mul(&a, &b, &c);
    assert(??a.to(u64) == 7020);

    // Aliasing
    %%b.set(i8, 5);
    %%c.set(i8, 4);
    %%Bn.mul(&a, &b, &c);
    assert(??a.to(u64) == 20);

    %%b.set(i8, 5);
    %%Bn.mul(&a, &b, &b);
    assert(??a.to(u64) == 25);

    %%a.set(i8, 4);
    %%b.set(i8, 5);
    %%Bn.mul(&a, &a, &b);
    assert(??a.to(u64) == 20);

    %%a.set(i8, 4);
    %%Bn.mul(&a, &a, &a);
    assert(??a.to(u64) == 16);
}

test "mulAlias" {
    var a = %%Bn.init();
    defer a.deinit();
    var b = %%Bn.init();
    defer b.deinit();

    %%a.set(i8, 5);
    %%b.set(i8, 5);
    %%Bn.mul(&a, &a, &b);
    assert(??a.to(u64) == 25);
}

test "mulMulti" {
    var a = %%Bn.init();
    defer a.deinit();
    %%a.setStr(16, "FFFFFFFF");

    var b = %%Bn.init();
    defer b.deinit();
    %%b.setStr(16, "FFFFFFFF");

    var c = %%Bn.init();
    defer c.deinit();

    %%Bn.mul(&c, &a, &b);
    // TODO: Implement toStr before assertions
}

test "divRemSingleLimb" {
    var a = %%Bn.init();
    defer a.deinit();
    var b = %%Bn.init();
    defer b.deinit();
    var q = %%Bn.init();
    defer q.deinit();
    var r = %%Bn.init();
    defer r.deinit();

    %%a.set(u8, 5);
    %%b.set(u8, 2);
    %%Bn.div(&q, &r, &a, &b);
    assert(??q.to(i64) == 2);
    assert(??r.to(i64) == 1);

    %%a.set(u16, 256);
    %%b.set(u8, 2);
    %%Bn.div(&q, &r, &a, &b);
    assert(??q.to(i64) == 128);
    assert(??r.to(i64) == 0);

    // 240530240918 / 324 = 742377286 r 254
    %%a.setStr(10, "240530240918");
    %%b.setStr(10, "324");
    %%Bn.div(&q, &r, &a, &b);
    assert(??q.to(u64) == 742377286);
    assert(??r.to(u64) == 254);
}


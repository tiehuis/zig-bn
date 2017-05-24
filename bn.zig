const std = @import("std");
const builtin = @import("builtin");
const assert = std.debug.assert;

const printf = std.io.stdout.printf;

error InvalidBase;
error ParseError;
error InputTooShort;

// TODO: Use addWithOverflow and friends instead so we can use wider (64-bit) base types.
pub const Limb = u32;
pub const DoubleLimb = @IntType(false, 2 * 8 * @sizeOf(Limb));
pub const Limbs = std.ArrayList(Limb);
pub const Cmp = std.math.Cmp;

// The default allocator to use for all subsequent Bn initializations.
const allocator = std.debug.global_allocator;

// Represents a single Big Number.
pub const Bn = struct {
    const Self = this;

    limbs: Limbs,
    positive: bool,

    pub fn init() -> Self {
        var limbs = Limbs.init(&std.debug.global_allocator);
        %%limbs.append(0);

        Self {
            .limbs = limbs,
            .positive = true
        }
    }

    pub fn deinit(self: &Self) {
        self.limbs.deinit();
    }

    pub fn toUInt(self: &Self) -> ?u64 {
        if (self.limbs.len == 1) {
            u64(self.limbs.items[0])
        } else {
            null
        }
    }

    // TODO: Handle underflow properly.
    pub fn toInt(self: &Self) -> ?i64 {
        if (self.limbs.len == 1) {
            const value = self.limbs.items[0];
            if (self.positive) i64(value) else -i64(value)
        } else {
            null
        }
    }

    pub fn set(self: &Self, comptime T: type, value: T) {
        comptime assert(@typeId(T) == builtin.TypeId.Int);
        comptime assert(@sizeOf(T) <= @sizeOf(Limb));   // TODO: Should allow halving 64-bit to 32-bit

        %%self.limbs.resize(1);

        if (!T.is_signed) {
            self.limbs.items[0] = Limb(value);
            self.positive = true;
        } else {
            // TODO: Determine API to handle underflow. Probably easiest to special case or handle
            // as a string the case of @minValue(Limb)
            self.limbs.items[0] = Limb(%%std.math.absInt(value));
            self.positive = false;
        }
    }

    pub fn zero(self: &Self) {
        // Always keep one limb available
        self.limbs.resizeDown(1);
        self.limbs.items[0] = 0;
    }

    // Zero-extend new allocation space in preparation for an operation.
    //
    // This modifies the actual array buffer content, and a `reduce` call should be performed after
    // the operation to reclaim any unused limbs.
    pub fn zeroExtend(self: &Self, n: usize) {
        const len = self.limbs.len;
        %%self.limbs.resize(n);

        var i = len;
        while (i <= self.limbs.len) : (i += 1) {
            self.limbs.items[i] = 0;
        }
    }

    // Reduce trailing zeroes that may exist following an operation.
    pub fn reduce(self: &Self) {
        // Always keep one limb available
        while (self.limbs.len != 1) {
            const item = self.limbs.pop();
            if (item != 0) {
                %%self.limbs.append(item);
                break;
            }
        }
    }

    // Converts a single character using the specified radix-map.
    fn convertBaseChar(value: u8, radix: u8) -> %u8 {
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

    // Set the big number to the value specified by the string.
    //
    // The input radix accepts values from the range [2, 62].
    // Digits are used first, then upper-case letters and finally lower-case letters.
    //
    // If an error occurs no guarantees are made about the resulting state of the Bn.
    pub fn set_str(self: &Self, base: u8, value: []const u8) -> %void {
        if (value.len == 0) {
            return error.InputTooShort;
        }
        if (base < 2 or base > 62) {
            return error.InvalidBase;
        }

        const approxLength = ((cilog2(base) * value.len) + 1) / (8 * @sizeOf(Limb)) + 1;
        self.zero();
        self.zeroExtend(approxLength);

        const tail = {
            if (value[0] != '-') {
                self.positive = true;
                value
            } else {
                self.positive = false;
                value[1..]
            }
        };

        var mult: Limb = 1;
        var carry: Limb = 0;
        var limb_index: usize = 0;

        // TODO: How to reverse iterate.
        for (tail) |_, i| {
            const d = %return convertBaseChar(value[value.len - i - 1], base);
            self.limbs.items[limb_index] = _muladd_limb_wc(self.limbs.items[limb_index], d, mult, &carry);

            if (carry != 0) {
                limb_index += 1;
                self.limbs.items[limb_index] = carry;
            }

            var result: Limb = undefined;
            if (@mulWithOverflow(Limb, mult, base, &result)) {
                limb_index += 1;
                mult = 1;
            } else {
                mult = result;
            }
        }

        self.reduce();
    }
};

fn cilog2(v: u64) -> u64 {
    var r: u64 = 0;
    var n: u64 = v; // Note: Input arguments are const by default.
    while (n != 0) : (n >>= 1) {
        r += 1;
    }
    r
}

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
        std.mem.cmp(Limb, a.limbs.toSlice(), b.limbs.toSlice())
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

// a + b + carry
//
// Carry is set to resulting overflow value.
fn _add_limb_wc(a: Limb, b: Limb, carry: &Limb) -> Limb {
    const result = DoubleLimb(a) + DoubleLimb(b) + DoubleLimb(*carry);
    *carry = @truncate(Limb, result >> 8 * @sizeOf(Limb));
    @truncate(Limb, result)
}

// a + b * c + carry
//
// Carry is set to resulting overflow value.
fn _muladd_limb_wc(a: Limb, b: Limb, c: Limb, carry: &Limb) -> Limb {
    const result = DoubleLimb(a) + DoubleLimb(b) * DoubleLimb(c) + DoubleLimb(*carry);
    *carry = @truncate(Limb, result >> 8 * @sizeOf(Limb));
    @truncate(Limb, result)
}

// a - b + borrow
//
// Carry is set to resulting underflow value.
fn _sub_limb_wb(a: Limb, b: Limb, borrow: &Limb) -> Limb {
    const base = DoubleLimb(1) << 8 * @sizeOf(Limb);
    const result = base + DoubleLimb(a) - DoubleLimb(b) - DoubleLimb(*borrow);
    const hi = @truncate(Limb, result >> 8 * @sizeOf(Limb));
    *borrow = Limb(hi == 0);
    @truncate(Limb, result)
}

fn _add3(dst: []Limb, a: []Limb, b: []Limb) {
    assert(a.len >= b.len);
    assert(dst.len >= a.len + 1);

    var carry: Limb = 0;
    for (a) |_, i| {
        dst[i] = _add_limb_wc(a[i], b[i], &carry);
    }

    if (carry != 0) {
        dst[a.len] = carry;
    }
}

// dst = a + b
pub fn add(dst: &Bn, a: &Bn, b: &Bn) {
    if (a.positive != b.positive) {
        if (a.positive) {
            b.positive = true;
            sub(dst, a, b);
            b.positive = false
        } else {
            a.positive = true;
            sub(dst, b, a);
            a.positive = false;
        }
    } else {
        if (a.limbs.len >= b.limbs.len) {
            dst.zeroExtend(a.limbs.len + 1);
            _add3(dst.limbs.items, a.limbs.toSlice(), b.limbs.toSlice());
            dst.reduce();
        } else {
            dst.zeroExtend(b.limbs.len + 1);
            _add3(dst.limbs.items, b.limbs.toSlice(), a.limbs.toSlice());
            dst.reduce();
        }

        dst.positive = a.positive;
    }
}

fn _sub3(dst: []Limb, a: []Limb, b: []Limb) {
    assert(a.len >= b.len);
    assert(dst.len >= b.len);

    var borrow: Limb = 0;
    for (b) |_, i| {
        dst[i] = _sub_limb_wb(a[i], b[i], &borrow);
    }
}

// dst = a - b
pub fn sub(dst: &Bn, a: &Bn, b: &Bn) {
    const cr = cmp(a, b);
    if (cr == Cmp.Greater) {
        dst.zeroExtend(b.limbs.len);
        _sub3(dst.limbs.items, a.limbs.toSlice(), b.limbs.toSlice());
        dst.reduce();
        dst.positive = true;
    } else if (cr == Cmp.Less) {
        dst.zeroExtend(a.limbs.len);
        _sub3(dst.limbs.items, b.limbs.toSlice(), a.limbs.toSlice());
        dst.reduce();
        dst.positive = false;
    } else {
        dst.set(u8, 0);
    }
}

// dst += a * b
//
// Perform a carrying multiplication spread into a limb slice. This can be thought of as a single
// pass over a multiplicative cross-product.
fn _muladd3_line(dst: []Limb, a: []Limb, b: Limb) {
    assert(dst.len >= a.len + 1);
    if (b == 0) {
        return;
    }

    var carry: Limb = 0;
    for (a) |_, i| {
        dst[i] += _muladd_limb_wc(dst[i], a[i], b, &carry);
    }

    if (carry != 0) {
        dst[a.len] = _muladd_limb_wc(dst[a.len], 0, b, &carry);
    }
}

pub fn _muladd3(dst: []Limb, a: []Limb, b: []Limb) {
    assert(dst.len >= a.len + b.len + 1);
    assert(a.len >= b.len);

    // Basecase multiplication always.
    //
    // Prefer broadcasting over the longer limb input instead of the short to use the longest
    // cache-lines and minimize function calls.
    for (b) |_, i| {
        _muladd3_line(dst[i..], a, b[i]);
    }
}

// dst = a * b
pub fn mul(dst: &Bn, a: &Bn, b: &Bn) {
    const sign = a == b;
    const a_sign = a.positive;
    const b_sign = b.positive;

    dst.zeroExtend(a.limbs.len + b.limbs.len + 1);
    a.positive = true;
    b.positive = true;

    dst.zero();

    if (a.limbs.len >= b.limbs.len) {
        _muladd3(dst.limbs.items, a.limbs.toSlice(), b.limbs.toSlice());
    } else {
        _muladd3(dst.limbs.items, b.limbs.toSlice(), a.limbs.toSlice());
    }

    dst.reduce();
    a.positive = a_sign;
    b.positive = b_sign;
    dst.positive = sign;
}

test "test_default_zero" {
    var a = Bn.init();
    defer a.deinit();

    assert(a.limbs.items[0] == 0);
    assert(a.positive);
}

test "test_from_int" {
    var a = Bn.init();
    defer a.deinit();

    a.set(u8, 5);
    assert(a.limbs.items[0] == 5);
    assert(a.positive == true);

    a.set(u16, @maxValue(u16));
    assert(a.limbs.items[0] == @maxValue(u16));
    assert(a.positive == true);

    a.set(i32, -5);
    assert(a.limbs.items[0] == 5);
    assert(a.positive == false);
}

test "test_to_int" {
    var a = Bn.init();
    defer a.deinit();
    assert(??a.toInt() == 0);

    a.limbs.items[0] = 5;
    a.positive = true;
    assert(??a.toUInt() == 5);
    assert(??a.toInt() == 5);

    a.limbs.items[0] = @maxValue(u16);
    a.positive = true;
    assert(??a.toUInt() == @maxValue(u16));

    a.limbs.items[0] = 5;
    a.positive = false;
    assert(??a.toInt() == -5);
}

test "test_to_str" {

    // Add overflow limb
}

test "test_from_str" {
    var a = Bn.init();
    defer a.deinit();

    %%a.set_str(10, "1");
    assert(??a.toInt() == 1);

    %%a.set_str(10, "1238");
    assert(??a.toInt() == 1238);

    %%a.set_str(10, "1230912412");
    assert(??a.toInt() == 1230912412);

    %%a.set_str(16, "FFFFFFFF");
    assert(??a.toUInt() == @maxValue(u32));

    // TODO: Remove test assumption that on size of limb.
    %%a.set_str(16, "FFFFFFFFFF");
    assert(a.limbs.items[0] == @maxValue(Limb));
    assert(a.limbs.items[1] == 0xFF);

    %%a.set_str(16, "FFEEFFEFAABBAABACCDDCCDC");
    assert(a.limbs.items[0] == 0xCCDDCCDC);
    assert(a.limbs.items[1] == 0xAABBAABA);
    assert(a.limbs.items[2] == 0xFFEEFFEF);

    %%a.set_str(10, "-10");
    assert(??a.toInt() == -10);

    // TODO: Requires compiler support for equality against errors
    //var r = a.set_str("A123");
    //assert(r == error.ParseError);
}

test "test_cmp" {
    var a = Bn.init();
    defer a.deinit();

    var b = Bn.init();
    defer b.deinit();

    a.set(u8, 0);
    b.set(u8, 1);
    assert(cmp(&a, &b) == Cmp.Less);

    a.set(u8, 1);
    b.set(u8, 0);
    assert(cmp(&a, &b) == Cmp.Greater);

    a.set(u8, 1);
    b.set(u8, 1);
    assert(cmp(&a, &b) == Cmp.Equal);
}

test "test_add_limb_wac" {
    var a: Limb = 3;
    var b: Limb = @maxValue(Limb);
    var c: Limb = 7;
    var d = _add_limb_wc(a, b, &c);

    assert(c == 1);
    assert(d == 9);
}

test "test_mul_limb_wc" {
    var a: Limb = 3;
    var b: Limb = @maxValue(Limb);
    var c: Limb = 7;
    var d = _add_limb_wc(a, b, &c);
}

test "test_sub_limb_wb" {
    var a: Limb = 5;
    var b: Limb = 4;
    var c: Limb = 3;
    var d = _sub_limb_wb(a, b, &c);

    assert(c == 1);
    assert(d == @maxValue(Limb) - 1);
}

test "test_sub_default" {
    var a = Bn.init();
    defer a.deinit();
    a.set(u32, 5);

    var b = Bn.init();
    defer b.deinit();
    b.set(u32, 5);

    var c = Bn.init();
    defer c.deinit();
    c.set(u32, 8);

    sub(&a, &c, &b);
    assert(??a.toInt() == 3);

    sub(&a, &b, &c);
    assert(??a.toInt() == -3);
}

test "test_add_default" {
    var a = Bn.init();
    defer a.deinit();
    a.set(u32, 5);

    var b = Bn.init();
    defer b.deinit();
    b.set(u32, 7);

    var c = Bn.init();
    defer c.deinit();
    c.set(u32, 13);

    add(&a, &b, &c);
    assert(??a.toUInt() == 20);

    add(&a, &c, &b);
    assert(??a.toUInt() == 20);

    add(&a, &c, &c);
    assert(??a.toUInt() == 26);

    add(&a, &a, &a);
    assert(??a.toUInt() == 52);
}

test "test_add_negative" {
    var a = Bn.init();
    defer a.deinit();
    a.set(u32, 5);

    var b = Bn.init();
    defer b.deinit();
    b.set(i32, -7);

    var c = Bn.init();
    defer c.deinit();
    c.set(u32, 13);

    add(&a, &b, &c);
    assert(??a.toUInt() == 6);

    add(&a, &c, &b);
    assert(??a.toUInt() == 6);

    b.set(i32, -14);
    c.set(i32, 13);
    add(&a, &b, &c);
    //%%std.io.stdout.printf("{}\n", ??a.toInt());
    //assert(??a.toInt() == -1);

    add(&a, &c, &b);
    //assert(??a.toInt() == -1);

    b.set(i32, -3);
    c.set(i32, -5);
    //assert(??a.toInt() == -8);
}

test "test_add_reallocate" {
}

test "test_mul_default" {
    var a = Bn.init();
    defer a.deinit();

    var b = Bn.init();
    defer b.deinit();

    var c = Bn.init();
    defer c.deinit();

    b.set(u8, 7);
    c.set(u8, 3);
    mul(&a, &b, &c);
    assert(??a.toUInt() == 21);

    b.set(u8, 90);
    c.set(u8, 78);
    mul(&a, &b, &c);
    assert(??a.toUInt() == 7020);

    b.set(i8, -90);
    c.set(u8, 78);
    mul(&a, &b, &c);
    assert(??a.toInt() == -7020);

    b.set(u8, 90);
    c.set(i8, -78);
    mul(&a, &b, &c);
    assert(??a.toInt() == -7020);

    b.set(i8, -90);
    c.set(i8, -78);
    mul(&a, &b, &c);
    assert(??a.toUInt() == 7020);
}

test "test_mul_reallocate" {
}

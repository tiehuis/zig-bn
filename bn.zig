const std = @import("std");
const builtin = @import("builtin");
const TypeId = builtin.TypeId;
const assert = std.debug.assert;
const printf = std.io.stdout.printf;

// Temporary for testing.
const Bn = BnWithAllocator(&std.debug.global_allocator);

// TODO: Use addWithOverflow and friends instead so we can use wider (64-bit) base types.
pub const Limb = u32;
pub const DoubleLimb = @IntType(false, 2 * 8 * @sizeOf(Limb));
pub const Limbs = std.ArrayList(Limb);
pub const Cmp = std.math.Cmp;

error InvalidBase;
error ParseError;
error InputTooShort;

pub fn BnWithAllocator(comptime allocator: &std.mem.Allocator) -> type {
    struct {
        const Self = this;

        limbs: Limbs,
        positive: bool,

        pub fn init() -> %Self {
            var limbs = Limbs.init(allocator);
            %return limbs.append(0);

            Self {
                .limbs = limbs,
                .positive = true
            }
        }

        pub fn deinit(self: &Self) {
            self.limbs.deinit();
        }

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

        // Set a Bn to zero.
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

        // Returns the number of bits required to represent the bignum.
        //
        // Negative values return the same count as their positive counterparts.
        pub fn bitLen(self: &Self) -> usize {
            assert(self.limbs.len > 0);
            const base_bits = 8 * @sizeOf(Limb) * (self.limbs.len - 1);
            base_bits + (8 * @sizeOf(Limb) - @clz(self.limbs.items[self.limbs.len - 1]))
        }

        pub fn abs(self: &Self) {
            self.positive = true;
        }

        pub fn neg(self: &Self) {
            self.positive = !self.positive;
        }

        pub fn isZero(self: &Self) -> bool {
            self.limbs.len == 1 and self.limbs.items[0] == 0
        }

        pub fn sign(self: &Self) -> isize {
            if (self.isZero()) {
                return 0;   // These return statements are required to avoid a compile error!
            } else if (self.positive) {
                return 1;
            } else {
                -1
            }
        }

        pub fn popcount(self: &Self) -> usize {
            var pop: usize = 0;
            for (self.limbs.toSliceConst()) |b| {
                pop += popcnt(b);
            }
            pop
        }

        // Set the big number to the value specified by the string.
        //
        // The input radix accepts values from the range [2, 62].
        // Digits are used first, then upper-case letters and finally lower-case letters.
        //
        // If an error occurs no guarantees are made about the resulting state of the Bn.
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

            const approxLength = ((cilog2(base) * value.len) + 1) / (8 * @sizeOf(Limb)) + 1;
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
                const d = %return convertBaseChar(item, base);
                %%mult.set(u8, d);
                %return add(self, self, &mult);
            }

            self.reduce();
        }
    }
}

fn popcnt(v: Limb) -> usize {
    var n: Limb = v;
    var sum: usize = 0;
    while (n != 0) : (n >>= 1) {
        sum += n & 1;
    }
    sum
}

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

// a + b + carry
//
// Carry is set to resulting overflow value.
fn _addLimbWc(a: Limb, b: Limb, carry: &Limb) -> Limb {
    const result = DoubleLimb(a) + DoubleLimb(b) + DoubleLimb(*carry);
    *carry = @truncate(Limb, result >> 8 * @sizeOf(Limb));
    @truncate(Limb, result)
}

// a + b * c + carry
//
// Carry is set to resulting overflow value.
fn _muladdLimbWc(a: Limb, b: Limb, c: Limb, carry: &Limb) -> Limb {
    const result = DoubleLimb(a) + DoubleLimb(b) * DoubleLimb(c) + DoubleLimb(*carry);
    *carry = @truncate(Limb, result >> 8 * @sizeOf(Limb));
    @truncate(Limb, result)
}

// a - b + borrow
//
// Carry is set to resulting underflow value.
fn _subLimbWb(a: Limb, b: Limb, borrow: &Limb) -> Limb {
    const base = DoubleLimb(1) << 8 * @sizeOf(Limb);
    const result = base + DoubleLimb(a) - DoubleLimb(b) - DoubleLimb(*borrow);
    const hi = @truncate(Limb, result >> 8 * @sizeOf(Limb));
    *borrow = Limb(hi == 0);
    @truncate(Limb, result)
}

// Divide a double sized Limb by a single Limb divisor.
//
// The quotient and remainder are stored in specified out variables.
// TODO: Tuples would be nice to have for something like this.
fn _div2LimbByLimb(q: &Limb, r: &Limb, hi: Limb, lo: Limb, d: Limb) {
    assert(hi < d);

    const lhs = (DoubleLimb(hi) << 8 * @sizeOf(Limb)) | (DoubleLimb(lo));
    const rhs = DoubleLimb(d);
    *q = Limb(lhs / rhs);
    *r = Limb(lhs % rhs);
}

// a / b where b is a single limb.
fn _divRemSingle(q: []Limb, r: &Limb, a: []const Limb, b: Limb) {
    assert(q.len >= a.len);
    *r = 0;

    for (a) |_, i| {
        const index = a.len - i - 1;
        _div2LimbByLimb(&q[index], r, *r, a[index], b);
    }
}

// TODO: Only handles single limb division right now!
pub fn div(q: &Bn, r: &Bn, a: &Bn, b: &Bn) -> %void {
    assert(!b.isZero());

    // Note: lots of possible aliasing here so double-check. May need copies.
    %return q.zeroExtend(a.limbs.len);
    r.zero();   // Reduce to single limb

    _divRemSingle(q.limbs.items, &r.limbs.items[0], a.limbs.toSliceConst(), b.limbs.items[0]);
    q.reduce();
}

fn _add3(dst: []Limb, a: []const Limb, b: []const Limb) {
    assert(a.len >= b.len);
    assert(dst.len >= a.len + 1);

    var carry: Limb = 0;
    for (b) |_, i| {
        dst[i] = _addLimbWc(a[i], b[i], &carry);
    }

    // Propagate carry across remaining a limbs
    for (a[b.len..]) |d, i| {
        dst[i] = _addLimbWc(a[i], 0, &carry);
        if (carry == 0) {
            break;
        }
    }
    if (carry != 0) {
        dst[a.len] = carry;
        carry = 0;
    }

    assert(carry == 0);
}

// dst = a + b
pub fn add(dst: &Bn, a: &Bn, b: &Bn) -> %void {
    if (a.positive != b.positive) {
        if (a.positive) {
            b.positive = true;
            %return sub(dst, a, b);
            b.positive = false
        } else {
            a.positive = true;
            %return sub(dst, b, a);
            a.positive = false;
        }
    } else {
        if (a.limbs.len >= b.limbs.len) {
            // if dst aliases a then we cannot use the slice itself, nor can we do an actual resize.
            %return dst.zeroExtend(a.limbs.len + 1);
            _add3(dst.limbs.items, a.limbs.toSliceConst(), b.limbs.toSliceConst());
            dst.reduce();
        } else {
            %return dst.zeroExtend(b.limbs.len + 1);
            _add3(dst.limbs.items, b.limbs.toSliceConst(), a.limbs.toSliceConst());
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
        dst[i] = _subLimbWb(a[i], b[i], &borrow);
    }
}

// dst = a - b
pub fn sub(dst: &Bn, a: &Bn, b: &Bn) -> %void {
    const cr = cmp(a, b);
    if (cr == Cmp.Greater) {
        %return dst.zeroExtend(b.limbs.len);
        _sub3(dst.limbs.items, a.limbs.toSlice(), b.limbs.toSlice());
        dst.reduce();
        dst.positive = true;
    } else if (cr == Cmp.Less) {
        %return dst.zeroExtend(a.limbs.len);
        _sub3(dst.limbs.items, b.limbs.toSlice(), a.limbs.toSlice());
        dst.reduce();
        dst.positive = false;
    } else {
        // Limb size will never be smaller than u8.
        %%dst.set(u8, 0);
    }
}

// dst += a * b
//
// Perform a carrying multiplication spread into a limb slice. This can be thought of as a single
// pass over a multiplicative cross-product.
fn muladd3Line(dst: []Limb, a: []const Limb, b: Limb) {
    assert(dst.len >= a.len + 1);
    if (b == 0) {
        return;
    }

    var carry: Limb = 0;
    for (a) |_, i| {
        dst[i] += _muladdLimbWc(dst[i], a[i], b, &carry);
    }

    if (carry != 0) {
        dst[a.len] = _muladdLimbWc(dst[a.len], 0, b, &carry);
    }
}

// dst must not alias either a or b.
// a and b can alias one another.
pub fn _muladd3(dst: []Limb, a: []const Limb, b: []const Limb) {
    assert(dst.len >= a.len + b.len + 1);
    assert(a.len >= b.len);

    // Basecase multiplication always.
    //
    // Prefer broadcasting over the longer limb input instead of the short to use the longest
    // cache-lines and minimize function calls.
    for (b) |_, i| {
        muladd3Line(dst[i..], a, b[i]);
    }
}

// dst = a * b
pub fn mul(dst: &Bn, a: &Bn, b: &Bn) -> %void{
    const a_sign = a.positive;
    const b_sign = b.positive;
    const sign = a_sign == b_sign;
    a.positive = true;
    b.positive = true;

    // TODO: Don't copy if non-alias.
    var temp = Limbs.init(&std.debug.global_allocator);
    defer temp.deinit();
    %return temp.resize(a.limbs.len + b.limbs.len + 1);

    if (a.limbs.len >= b.limbs.len) {
        _muladd3(temp.items, a.limbs.toSliceConst(), b.limbs.toSliceConst());
    } else {
        _muladd3(temp.items, b.limbs.toSliceConst(), a.limbs.toSliceConst());
    }

    for (temp.items) |item, i| { dst.limbs.items[i] = item }
    dst.reduce();

    a.positive = a_sign;
    b.positive = b_sign;
    dst.positive = sign;
}

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

test "cmp" {
    var a = %%Bn.init();
    defer a.deinit();

    var b = %%Bn.init();
    defer b.deinit();

    %%a.set(u8, 0);
    %%b.set(u8, 1);
    assert(cmp(&a, &b) == Cmp.Less);

    %%a.set(u8, 1);
    %%b.set(u8, 0);
    assert(cmp(&a, &b) == Cmp.Greater);

    %%a.set(u8, 1);
    %%b.set(u8, 1);
    assert(cmp(&a, &b) == Cmp.Equal);
}

test "_addLimbWc" {
    var a: Limb = 3;
    var b: Limb = @maxValue(Limb);
    var c: Limb = 7;
    var d = _addLimbWc(a, b, &c);

    assert(c == 1);
    assert(d == 9);
}

test "_muladdLimbWc" {
}

test "_subLimbWb" {
    var a: Limb = 5;
    var b: Limb = 4;
    var c: Limb = 3;
    var d = _subLimbWb(a, b, &c);

    assert(c == 1);
    assert(d == @maxValue(Limb) - 1);
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

    %%sub(&a, &c, &b);
    assert(??a.to(i64) == 3);

    %%sub(&a, &b, &c);
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

    %%add(&a, &b, &c);
    assert(??a.to(u64) == 20);

    %%add(&a, &c, &b);
    assert(??a.to(u64) == 20);

    %%add(&a, &c, &c);
    assert(??a.to(u64) == 26);

    %%add(&a, &a, &a);
    assert(??a.to(u64) == 52);

    %%add(&a, &a, &b);
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

    %%add(&a, &b, &c);
    assert(??a.to(u64) == 6);

    %%add(&a, &c, &b);
    assert(??a.to(u64) == 6);

    %%b.set(i32, -14);
    %%c.set(i32, 13);
    %%add(&a, &b, &c);
    //assert(??a.to(i64) == -1);

    %%add(&a, &c, &b);
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

    %%add(&c, &a, &b);
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
    %%mul(&a, &a, &b);
    assert(??a.to(u64) == 25);

    %%b.set(u8, 7);
    %%c.set(u8, 3);
    %%mul(&a, &b, &c);
    assert(??a.to(u64) == 21);

    %%b.set(u8, 90);
    %%c.set(u8, 78);
    %%mul(&a, &b, &c);
    assert(??a.to(u64) == 7020);

    %%b.set(i8, -90);
    %%c.set(u8, 78);
    %%mul(&a, &b, &c);
    assert(??a.to(i64) == -7020);

    %%b.set(u8, 90);
    %%c.set(i8, -78);
    %%mul(&a, &b, &c);
    assert(??a.to(i64) == -7020);

    %%b.set(i8, -90);
    %%c.set(i8, -78);
    %%mul(&a, &b, &c);
    assert(??a.to(u64) == 7020);
}

test "mulAlias" {
    var a = %%Bn.init();
    defer a.deinit();
    var b = %%Bn.init();
    defer b.deinit();

    %%a.set(i8, 5);
    %%b.set(i8, 5);
    %%mul(&a, &a, &b);
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

    %%mul(&c, &a, &b);
    // TODO: Implement toStr before assertions
}

test "_divRemSingle" {
    var q: [2]Limb = undefined;
    var r: Limb = undefined;

    var a: [2]Limb = undefined;
    var b: Limb = undefined;

    a[1] = 0;
    a[0] = 4;
    b = 2;
    _divRemSingle(q[0..2], &r, a[0..2], b);
    assert(q[1] == 0);
    assert(q[0] == 2);
    assert(r == 0);

    a[1] = 0;
    a[0] = 987;
    b = 13;
    _divRemSingle(q[0..2], &r, a[0..2], b);
    assert(q[1] == 0);
    assert(q[0] == 75);
    assert(r == 12);

    // 240530240918 / 324 = 742377286 r 254
    a[1] = 56;
    a[0] = 12072342;
    b = 324;
    _divRemSingle(q[0..2], &r, a[0..2], b);
    assert(q[1] == 0);
    assert(q[0] == 742377286);
    assert(r == 254);
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
    %%div(&q, &r, &a, &b);
    assert(??q.to(i64) == 2);
    assert(??r.to(i64) == 1);

    %%a.set(u16, 256);
    %%b.set(u8, 2);
    %%div(&q, &r, &a, &b);
    assert(??q.to(i64) == 128);
    assert(??r.to(i64) == 0);

    // 240530240918 / 324 = 742377286 r 254
    %%a.setStr(10, "240530240918"); // not setting correctly due to mul alias??
    %%b.setStr(10, "324");
    %%div(&q, &r, &a, &b);
//    assert(??q.to(u64) == 742377286);
 //   assert(??r.to(u64) == 254);
}


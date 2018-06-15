const std = @import("std");
const builtin = @import("builtin");
const debug = std.debug;
const math = std.math;
const mem = std.mem;
const Allocator = mem.Allocator;
const ArrayList = std.ArrayList;

const TypeId = builtin.TypeId;

use @import("int.zig");

pub const Rational = struct {
    // sign of Rational is a.positive, b.positive is ignored
    p: Int,
    q: Int,

    pub fn init(a: *Allocator) !Rational {
        return Rational{
            .p = try Int.init(a),
            .q = try Int.initSet(a, 1),
        };
    }

    pub fn deinit(self: *const Rational) void {
        self.p.deinit();
        self.q.deinit();
    }

    pub fn setInt(self: *Rational, a: var) !void {
        try self.p.set(a);
        try self.q.set(1);
    }

    pub fn setRatio(self: *Rational, p: var, q: var) !void {
        try self.p.set(p);
        try self.q.set(q);

        self.p.positive = (u8(self.p.positive) ^ u8(self.q.positive)) == 0;
        self.q.positive = true;
        try self.reduce();

        if (self.q.eqZero()) {
            @panic("cannot set rational with denominator = 0");
        }
    }

    pub fn copyInt(self: *Rational, a: *const Int) !void {
        try self.p.copy(a);
        try self.q.set(1);
    }

    pub fn copyRatio(self: *Rational, a: *const Int, b: *const Int) !void {
        try self.p.copy(a);
        try self.q.copy(b);

        self.p.positive = (u8(self.p.positive) ^ u8(self.q.positive)) == 0;
        self.q.positive = true;
        try self.reduce();
    }

    pub fn abs(r: *Rational) void {
        r.p.abs();
    }

    pub fn negate(r: *Rational) void {
        r.p.negate();
    }

    pub fn swap(r: *Rational, other: *Rational) void {
        r.p.swap(&other.p);
        r.q.swap(&other.q);
    }

    pub fn cmp(a: *const Rational, b: *const Rational) !i8 {
        return cmpInternal(a, b, true);
    }

    pub fn cmpAbs(a: *const Rational, b: *const Rational) !i8 {
        return cmpInternal(a, b, false);
    }

    // p/q > x/y iff p*y > x*q
    fn cmpInternal(a: *const Rational, b: *const Rational, is_abs: bool) !i8 {
        // TODO: Maybe use divexact and perform p/q and x/y directly to save on memory for
        // large limbs instead of performing a mul. Check performance difference.
        var q = try Int.init(a.p.allocator);
        defer q.deinit();

        var p = try Int.init(b.p.allocator);
        defer p.deinit();

        try q.mul(&a.p, &b.q);
        try p.mul(&b.p, &a.q);

        return if (is_abs) q.cmpAbs(&p) else q.cmp(&p);
    }

    // r/q = ap/aq + bp/bq = (ap*bq + bp*aq) / (aq*bq)
    //
    // For best performance, rma should not alias a or b.
    pub fn add(rma: *Rational, a: *const Rational, b: *const Rational) !void {
        var r = rma;
        var aliased = rma == a or rma == b;

        var sr: Rational = undefined;
        if (aliased) {
            sr = try Rational.init(rma.p.allocator);
            r = &sr;
            aliased = true;
        }
        defer if (aliased) {
            rma.swap(r);
            r.deinit();
        };

        try r.p.mul(&a.p, &b.q);
        try r.q.mul(&b.p, &a.q);
        try r.p.add(&r.p, &r.q);

        try r.q.mul(&a.q, &b.q);
        try r.reduce();
    }

    // r/q = ap/aq - bp/bq = (ap*bq - bp*aq) / (aq*bq)
    //
    // For best performance, rma should not alias a or b.
    pub fn sub(rma: *Rational, a: *const Rational, b: *const Rational) !void {
        var r = rma;
        var aliased = rma == a or rma == b;

        var sr: Rational = undefined;
        if (aliased) {
            sr = try Rational.init(rma.p.allocator);
            r = &sr;
            aliased = true;
        }
        defer if (aliased) {
            rma.swap(r);
            r.deinit();
        };

        try r.p.mul(&a.p, &b.q);
        try r.q.mul(&b.p, &a.q);
        try r.p.sub(&r.p, &r.q);

        try r.q.mul(&a.q, &b.q);
        try r.reduce();
    }

    // r/q = ap/aq * bp/bq = ap*bp / aq*bq
    pub fn mul(r: *Rational, a: *const Rational, b: *const Rational) !void {
        try r.p.mul(&a.p, &b.p);
        try r.q.mul(&a.q, &b.q);
        try r.reduce();
    }

    // r/q = (ap/aq) / (bp/bq) = ap*bq / bp*aq
    pub fn div(r: *Rational, a: *const Rational, b: *const Rational) !void {
        if (b.p.eqZero()) {
            @panic("division by zero");
        }

        try r.p.mul(&a.p, &b.q);
        try r.q.mul(&b.p, &a.q);
        try r.reduce();
    }

    // r/q = q/r
    pub fn invert(r: *Rational) void {
        Int.swap(&r.p, &r.q);
    }

    // reduce r/q such that gcd(r, q) = 1
    fn reduce(r: *Rational) !void {
        var a = try Int.init(r.p.allocator);
        defer a.deinit();

        const sign = r.p.positive;

        r.p.abs();
        try gcd(&a, &r.p, &r.q);
        r.p.positive = sign;

        if (a.cmp(1) != 0) {
            var unused = try Int.init(r.p.allocator);
            defer unused.deinit();

            // TODO: divexact would be useful here
            // TODO: don't copy r.q for div
            try Int.divTrunc(&r.p, &unused, &r.p, &a);
            try Int.divTrunc(&r.q, &unused, &r.q, &a);
        }
    }
};

var al = debug.global_allocator;

test "big.rational set" {
    var a = try Rational.init(al);

    try a.setInt(5);
    debug.assert((try a.p.to(u32)) == 5);
    debug.assert((try a.q.to(u32)) == 1);

    try a.setRatio(7, 3);
    debug.assert((try a.p.to(u32)) == 7);
    debug.assert((try a.q.to(u32)) == 3);

    try a.setRatio(9, 3);
    debug.assert((try a.p.to(i32)) == 3);
    debug.assert((try a.q.to(i32)) == 1);

    try a.setRatio(-9, 3);
    debug.assert((try a.p.to(i32)) == -3);
    debug.assert((try a.q.to(i32)) == 1);

    try a.setRatio(9, -3);
    debug.assert((try a.p.to(i32)) == -3);
    debug.assert((try a.q.to(i32)) == 1);

    try a.setRatio(-9, -3);
    debug.assert((try a.p.to(i32)) == 3);
    debug.assert((try a.q.to(i32)) == 1);
}

test "big.rational copy" {
    var a = try Rational.init(al);

    const b = try Int.initSet(al, 5);

    try a.copyInt(&b);
    debug.assert((try a.p.to(u32)) == 5);
    debug.assert((try a.q.to(u32)) == 1);

    const c = try Int.initSet(al, 7);
    const d = try Int.initSet(al, 3);

    try a.copyRatio(&c, &d);
    debug.assert((try a.p.to(u32)) == 7);
    debug.assert((try a.q.to(u32)) == 3);

    const e = try Int.initSet(al, 9);
    const f = try Int.initSet(al, 3);

    try a.copyRatio(&e, &f);
    debug.assert((try a.p.to(u32)) == 3);
    debug.assert((try a.q.to(u32)) == 1);
}

test "big.rational negate" {
    var a = try Rational.init(al);

    try a.setInt(-50);
    debug.assert((try a.p.to(i32)) == -50);
    debug.assert((try a.q.to(i32)) == 1);

    a.negate();
    debug.assert((try a.p.to(i32)) == 50);
    debug.assert((try a.q.to(i32)) == 1);

    a.negate();
    debug.assert((try a.p.to(i32)) == -50);
    debug.assert((try a.q.to(i32)) == 1);
}

test "big.rational abs" {
    var a = try Rational.init(al);

    try a.setInt(-50);
    debug.assert((try a.p.to(i32)) == -50);
    debug.assert((try a.q.to(i32)) == 1);

    a.abs();
    debug.assert((try a.p.to(i32)) == 50);
    debug.assert((try a.q.to(i32)) == 1);

    a.abs();
    debug.assert((try a.p.to(i32)) == 50);
    debug.assert((try a.q.to(i32)) == 1);
}

test "big.rational swap" {
    var a = try Rational.init(al);
    var b = try Rational.init(al);

    try a.setRatio(50, 23);
    try b.setRatio(17, 3);

    debug.assert((try a.p.to(u32)) == 50);
    debug.assert((try a.q.to(u32)) == 23);

    debug.assert((try b.p.to(u32)) == 17);
    debug.assert((try b.q.to(u32)) == 3);

    a.swap(&b);

    debug.assert((try a.p.to(u32)) == 17);
    debug.assert((try a.q.to(u32)) == 3);

    debug.assert((try b.p.to(u32)) == 50);
    debug.assert((try b.q.to(u32)) == 23);
}

test "big.rational cmp" {
    var a = try Rational.init(al);
    var b = try Rational.init(al);

    try a.setRatio(500, 231);
    try b.setRatio(18903, 8584);
    debug.assert((try a.cmp(&b)) < 0);

    try a.setRatio(890, 10);
    try b.setRatio(89, 1);
    debug.assert((try a.cmp(&b)) == 0);
}

test "big.rational add single-limb" {
    var a = try Rational.init(al);
    var b = try Rational.init(al);

    try a.setRatio(500, 231);
    try b.setRatio(18903, 8584);
    debug.assert((try a.cmp(&b)) < 0);

    try a.setRatio(890, 10);
    try b.setRatio(89, 1);
    debug.assert((try a.cmp(&b)) == 0);
}

test "big.rational add" {
    var a = try Rational.init(al);
    var b = try Rational.init(al);
    var r = try Rational.init(al);

    try a.setRatio(78923, 23341);
    try b.setRatio(123097, 12441414);
    try a.add(&a, &b);

    try r.setRatio(984786924199, 290395044174);
    debug.assert((try a.cmp(&r)) == 0);
}

test "big.rational sub" {
    var a = try Rational.init(al);
    var b = try Rational.init(al);
    var r = try Rational.init(al);

    try a.setRatio(78923, 23341);
    try b.setRatio(123097, 12441414);
    try a.sub(&a, &b);

    try r.setRatio(979040510045, 290395044174);
    debug.assert((try a.cmp(&r)) == 0);
}

test "big.rational mul" {
    var a = try Rational.init(al);
    var b = try Rational.init(al);
    var r = try Rational.init(al);

    try a.setRatio(78923, 23341);
    try b.setRatio(123097, 12441414);
    try a.mul(&a, &b);

    try r.setRatio(571481443, 17082061422);
    debug.assert((try a.cmp(&r)) == 0);
}

test "big.rational div" {
    var a = try Rational.init(al);
    var b = try Rational.init(al);
    var r = try Rational.init(al);

    try a.setRatio(78923, 23341);
    try b.setRatio(123097, 12441414);
    try a.div(&a, &b);

    try r.setRatio(75531824394, 221015929);
    debug.assert((try a.cmp(&r)) == 0);
}

test "big.rational div" {
    var a = try Rational.init(al);
    var r = try Rational.init(al);

    try a.setRatio(78923, 23341);
    a.invert();

    try r.setRatio(23341, 78923);
    debug.assert((try a.cmp(&r)) == 0);

    try a.setRatio(-78923, 23341);
    a.invert();

    try r.setRatio(-23341, 78923);
    debug.assert((try a.cmp(&r)) == 0);
}

const SignedDoubleLimb = @IntType(true, DoubleLimb.bit_count);

fn gcd(rma: *Int, x: *const Int, y: *const Int) !void {
    var r = rma;
    var aliased = rma == x or rma == y;

    var sr: Int = undefined;
    if (aliased) {
        sr = try Int.initCapacity(rma.allocator, math.max(x.len, y.len));
        r = &sr;
        aliased = true;
    }
    defer if (aliased) {
        rma.swap(r);
        r.deinit();
    };

    if (x.cmp(y) > 0) {
        try gcdLehmer(r, x, y);
    } else {
        try gcdLehmer(r, y, x);
    }
}

fn gcdLehmer(r: *Int, xa: *const Int, ya: *const Int) !void {
    debug.assert(xa.positive and ya.positive);
    debug.assert(xa.cmp(ya) >= 0);

    var x = try xa.clone();
    defer x.deinit();

    var y = try ya.clone();
    defer y.deinit();

    var T = try Int.init(r.allocator);
    defer T.deinit();

    //while (y.limbs.len > 1) {
    //    var xh: SignedDoubleLimb = x.limbs[x.len - 1];
    //    var yh: SignedDoubleLimb = y.limbs[y.len - 1];

    //    var A: SignedDoubleLimb = 1;
    //    var B: SignedDoubleLimb = 0;
    //    var C: SignedDoubleLimb = 0;
    //    var D: SignedDoubleLimb = 1;

    //    while (yh + C != 0 and yh + D != 0) {
    //        const q = @divFloor(xh + A, yh + C);
    //        const qp = @divFloor(xh + B, yh + D);
    //        if (q != qp) {
    //            break;
    //        }

    //        // All these are single limbs, can we use a DoubleLimb signed?
    //        var t = A - q * C;
    //        A = C;
    //        C = t;
    //        t = B - q * D;
    //        B = D;
    //        D = t;

    //        t = xh - q * yh;
    //        xh = yh;
    //        yh = t;
    //    }

    //    if (B == 0) {
    //        // T = x % y, r is unused
    //        try Int.divTrunc(r, &T, x, y);
    //        debug.assert(T.positive);

    //        x.swap(&y);
    //        y.swap(&T);
    //    } else {
    //        // T = Ax + By
    //        try r.mul(x, A);
    //        try T.mul(y, B);
    //        try T.add(r, &T);

    //        // u = Cx + Dy, r as u
    //        try x.mul(x, C);
    //        try r.mul(y, D);
    //        try r.add(x, r);

    //        x.swap(&T);
    //        y.swap(r);
    //    }
    //}

    // euclidean algorithm
    debug.assert(x.cmp(y) >= 0);

    while (!y.eqZero()) {
        try Int.divTrunc(&T, r, &x, &y);
        x.swap(&y);
        y.swap(r);
    }

    r.swap(&x);
}

test "big.rational gcd non-one small" {
    var a = try Int.initSet(al, 17);
    var b = try Int.initSet(al, 97);
    var r = try Int.init(al);

    try gcd(&r, &a, &b);

    debug.assert((try r.to(u32)) == 1);
}

test "big.rational gcd non-one small" {
    var a = try Int.initSet(al, 4864);
    var b = try Int.initSet(al, 3458);
    var r = try Int.init(al);

    try gcd(&r, &a, &b);

    debug.assert((try r.to(u32)) == 38);
}

test "big.rational gcd non-one large" {
    var a = try Int.initSet(al, 0xffffffffffffffff);
    var b = try Int.initSet(al, 0xffffffffffffffff7777);
    var r = try Int.init(al);

    try gcd(&r, &a, &b);

    debug.assert((try r.to(u32)) == 4369);
}

const u256 = @IntType(false, 256);

test "big.rational gcd large multi-limb result" {
    var a = try Int.initSet(al, 0x12345678123456781234567812345678123456781234567812345678);
    var b = try Int.initSet(al, 0x12345671234567123456712345671234567123456712345671234567);
    var r = try Int.init(al);

    try gcd(&r, &a, &b);

    debug.assert((try r.to(u256)) == 0xf000000ff00000fff0000ffff000fffff00ffffff1);
}

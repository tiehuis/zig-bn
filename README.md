An (unfinished) arbitrary precision big number library for [zig](http://ziglang.org/).

The interface is akin to that of GMP.

```
const bn = @import("bn.zig");
const Bn = bn.Bn;

pub fn main() -> %void {
    var a = Bn.init();
    defer a.deinit();
    var b = Bn.init();
    defer b.deinit();

    a.setStrRadix(10, "1990273423429836742364234234234");
    b.setStrRadix(10, "1990273423429836742364234234234");

    bn.add(&a, &a, &b);

    var result = a.toString();
    defer result.deinit();
    %%io.stdout.printf("{}\n", result);
}
```

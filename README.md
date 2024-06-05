# BubbleTea
A fun interpreted toy language written in Rust!

![bubbletealogobig](https://github.com/LieutenantTeaTM/BubbleTea/assets/112296448/bace29c8-0355-4739-8e16-1639a858b199)

BubbleTea focuses on syntactic minimalism. Code should be simple and fun.

### To-Do
- [ ] Online Playground
- [ ] Bug Fixes
- [ ] Better List Support

BubbleTea is interpreted and dynamically typed, providing accessibility for anyone, BubbleTea closer resembles a scripting language rather than a full programming language.

## Example syntax:

**Example 1)**
```
fn main() {
  v x: 2;
  p(2 + 2);
}
```

**Example 2)**
```
fn test(x) {
    for i in x + 24 {
        p(i);
        if i :: 6 {
            break;
            p("");
        }
    }
}

fn main() {
    v x: 26.5;
    test(x);
}
```

**Example 3)**
```
fn f(x, y) {
  x + y
} 

fn main() {
  p(f(2, 3));
}
```

Have fun!

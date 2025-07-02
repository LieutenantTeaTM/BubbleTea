# BubbleTea
A minimalist programming language that transpiles directly to Rust with embedded language features.

![bubbletealogobig](https://github.com/LieutenantTeaTM/BubbleTea/assets/112296448/bace29c8-0355-4739-8e16-1639a858b199)

BubbleTea is a hobby language mostly targeted for recreational/hobby programming. It is lexed and parsed by a custom Lexer and Parser, then each instruction is transpiled into native Rust code and bundled into an executable. It is high level and simple. It also allows for running arbitrary Rust code directly within it, thus allowing the use for an embedded language.

### To-Do
- [ ] Bug fixes
- [ ] Arrays/Vectors
- [ ] Proper Examples

### Features
- [x] Static Typing
- [x] Syntax minimalism
- [x] Constant by default variables 
- [x] User-defined custom macros for running Rust code
- [x] Transpiling down to native Rust code without needing to use Rust   

**Note:** *Requires the Rust compiler to be installed and working.*

## Syntax Examples
```
fn main() -> null {
  v x: int -> 6;
  p!(x % 2);
}
```

```
fn main() -> null {
  p!(add(25.0, 25.0));
}

fn add(x: float, y: float) -> float {
  <- x + y * 2.5;
}
```

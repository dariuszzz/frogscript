toy programming language

# Syntax overview
```
// Comments
/*
multiline
comments
*/

// Variables
let int immutable_variable = 23
mut string mutable_variable = ""
let inferred_type = 34 // of type int

// Literals
let int_literal = 2340
let int_suffix = 59i
let uint_literal = 24u
let float_literal = 592.24
let float_suffix = 93f
let string_literal = "hello"
let bool_literal = true
let bool_literal2 = false
let array_literal = []
let array_literal2 = [1, 2, 3]

// Placeholder
// temporary value always valid
let foo = ...

// Formatted string
let num = 24
let fstring = "{num}" // of type string and value "24"

// Binary operations
let add = 2 + 3
let sub = 2 - 3
let mul = 2 * 3
let div = 2 / 3
let eq  = 3 == 3
let neq = 3 != 4

// Shorthands
add += 3
sub -= 50
mul *= 23
div /= 59

// Unary operations
mut b = true
b = !b // false
b = !b // true again

let num = 23
let num2 = -num // -23

// Type definitions
type Foo = int // opaque alias not synonymous with int

type Bar =
  field1 int
  field2 string

// Functions
fn no_args = return 54
fn args(x int, y string) = return "{string}{x}"
fn return_ty -> string =
  return "hello"
fn return_args(x int) -> string =
  let y = x * 20
  return "{y}"

  // can omit commas
fn many_args(
  x int
  y int
  z int
) = ...

// Lambdas
let f = fn(x) return x * 2

let f2 = fn(x int) -> int
  return x * 2

let fn(int -> int) f3 = f2
let fn(int, int -> int) f4 = fn(x int, y int) -> int return x + y

// Working with types
type Baz =
  field string

let obj = Baz { field: "hello" }
core::print(obj.field) // prints "hello"

// Working with arrays
let arr = [1, 2, 3]
//can omit commas
let arr2 = [
  1
  2
  3
]

let elem = arr2[2] // 3

// If statements
if 2 == 4:
  core::print("Impossible")
else // no colon
  core::print("Everything fine")

if false:
  ...
else if false:
  ...
else
  core::print("finally!")

// For loops
for i in [0, 1, 2]:
  core::print(i)

// Ranges
for i in 0..3:
  core::print(i) // same as above

for i in 0..=3:
  core::print(i) // prints up to 3

// Nested modules
module Mod =
  fn foo() = ...
  fn baz() = ...

<name_of_file>::Mod::foo()

// Use statements
use core::print

print(2) // no need to do core::print now

use <name_of_file>::Mod::foo

foo() // same as earlier

// could also do

use <name_of_file>::Mod {
  foo,
  baz
}

foo()
baz()

// Injecting js
@instr("console.log(32)") // will transpile to "console.log(32)"

let num = 59
@instr("console.log({num})") // will transpile to console.log(num)
```

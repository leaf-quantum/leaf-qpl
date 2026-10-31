### Boolean Literals

```leaf
false
true
```

### Quantum State Literals

```leaf
one
minus
minusi
plus
plusi
zero
```

### Leaf Keywords

```leaf
affine
as
break
classical
coisometry
const
continue
else
ensures
enum
fn
for
general
if
impl
in
isometry
let
linear
loop
match
mod
mut
pub
qif
qelse
qenum
qmatch
requires
return
scratch
self
selse
sif
smatch
struct
supports
then
unitary
uncompsafe
use
while
```

### Adjoint

Keyword usable as both a higher-order operator and a block operator:

```leaf
adjoint()
adjoint {
    // block of code
}
```

### Leaf Reserved Built-in Functions

Built-in Functions CANNOT be shadowed by a local declaration:

```leaf
adjoint
barrier
ctrl + on + apply
basis
clean
discard
isolated
len
measr
product
qalloc
reset
rev
tensor
separable
stabilized
uncompute
weaken
```

### Leaf Prelude Functions

Prelude functions CAN be shadowed by a local declaration:

```leaf
abs
acos
asin
atan
ceil
cos
exp
floor
ln
log2
log10
max
min
Param
phase
round
sin
sqrt
tan
turns
```

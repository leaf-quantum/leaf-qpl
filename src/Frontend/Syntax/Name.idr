module Frontend.Syntax.Name

import Frontend.ASTPhases
import Frontend.ASTData

%default total

--------------------------------------------------------------------------------
-- Names
--------------------------------------------------------------------------------
-- Every node family below is indexed by `phase : AstPhase`. What actually 
-- changes across phases:
--
--   * SurfaceAstPhase / CanonicalAstPhase -- a name is just its written text. Desugaring
--     never invents or resolves names, so CanonicalAstPhase reuses SurfaceAstPhase's
--     payload unchanged.
--   * ResolvedAstPhase / TypedAstPhase -- a name additionally carries the SymbolId it
--     resolved to.
--
-- This does NOT resolve names itself -- it does not decide whether a name
-- denotes a local variable, function, type, enum variant, module, field,
-- method, or associated function. It preserves source locations so every
-- phase can report diagnostics against the exact written name/path.
--
-- Examples represented by these types:
--
--   x
--   q
--   helper
--   my_library::helper
--   Data::Left
--   Person::new
--
-- Builtins such as qalloc, measr, reset, ctrl, apply, etc. are not modeled
-- here as ordinary names if the lexer classifies them as TokBuiltin.
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- Simple names
--------------------------------------------------------------------------------

public export
record NameNode where
  constructor MkNameNode
  nameNodeText : String

-- SymbolId identifies the program entity (variable, function, struct, enum, module) that this name denotes
public export
record ResolvedNameNode where
  constructor MkResolvedNameNode
  nameNodeText     : String
  nameNodeSymbolId : SymbolId

public export
NameFor : AstPhase -> Type
NameFor SurfaceAstPhase   = NameNode
NameFor CanonicalAstPhase = NameNode
NameFor ResolvedAstPhase  = ResolvedNameNode
NameFor TypedAstPhase     = ResolvedNameNode

-- method calls (occur in structs, enums and primitive types)
-- fields (can occur attached to structs, tuple structs, tuples, and enum variants)
public export
MemberNameFor : AstPhase -> Type
MemberNameFor SurfaceAstPhase   = NameNode
MemberNameFor CanonicalAstPhase = NameNode
MemberNameFor ResolvedAstPhase  = NameNode
MemberNameFor TypedAstPhase     = ResolvedNameNode

public export
Name : AstPhase -> Type
Name phase = AstNode phase (NameFor phase)

public export
SurfaceName : Type
SurfaceName = Name SurfaceAstPhase

public export
CanonicalName : Type
CanonicalName = Name CanonicalAstPhase

public export
ResolvedName : Type
ResolvedName = Name ResolvedAstPhase

public export
TypedName : Type
TypedName = Name TypedAstPhase

public export
MemberName : AstPhase -> Type
MemberName phase = AstNode phase (MemberNameFor phase)

--------------------------------------------------------------------------------
-- `self`
--------------------------------------------------------------------------------
-- `self` (ExprSelf in AST.idr) has no written spelling to preserve -- it is
-- always the keyword -- so unlike NameFor there is no NameNode-shaped payload
-- before resolution. What resolution adds is exactly what it adds to every
-- other name occurrence: the SymbolId of the enclosing method's receiver
-- parameter (SymbolSelfReceiverParameter in ASTData.idr), so a `self`
-- occurrence is self-describing after resolution -- like ExprName/ExprPath --
-- instead of forcing every consumer to re-derive it from nodeScopes by
-- re-walking the enclosing scope chain looking for the one binding of kind
-- SymbolSelfReceiverParameter.
--
-- Not wrapped in `AstNode phase (...)` the way Name/MemberName are: ExprSelf
-- is already located by its own enclosing AstNode, and there is no separate
-- span to give the SymbolId of its own.
--------------------------------------------------------------------------------

public export
SelfFor : AstPhase -> Type
SelfFor SurfaceAstPhase   = ()
SelfFor CanonicalAstPhase = ()
SelfFor ResolvedAstPhase  = SymbolId
SelfFor TypedAstPhase     = SymbolId

--------------------------------------------------------------------------------
-- Path segments
--------------------------------------------------------------------------------
-- A path segment is one component of a Rust-style :: path.
--
-- Examples:
--
--   my_library::helper
--   ^^^^^^^^^^  ^^^^^^
--   segment     segment
--
--   Data::Left
--   ^^^^  ^^^^
--   segment segment
--
-- The `self` keyword is syntactically special in Leaf and lexed as a
-- keyword, not an ordinary identifier, so it gets its own segment
-- constructor. Segments are phase-invariant TEXT before resolution
-- collapses a whole path into ResolvedPathNode below, so there is no
-- `PathSegmentFor` -- only SurfaceAstPhase and CanonicalAstPhase ever wrap a
-- `PathSegmentNode` directly.
--------------------------------------------------------------------------------

public export
data PathSegmentNode
  = PathSegmentName String
  | PathSegmentSelf

public export
PathSegment : AstPhase -> Type
PathSegment phase = AstNode phase PathSegmentNode

public export
SurfacePathSegment : Type
SurfacePathSegment = PathSegment SurfaceAstPhase

public export
CanonicalPathSegment : Type
CanonicalPathSegment = PathSegment CanonicalAstPhase

--------------------------------------------------------------------------------
-- Paths
--------------------------------------------------------------------------------
-- A Path represents one or more path segments separated by `::`.
--
-- The AST enforces the basic syntactic invariant that a path is non-empty.
--
-- Examples:
--
--   x
--   my_library::helper
--   Data::Left
--   Person::new
--
-- A single identifier like `x` can be represented as a path with one
-- segment, but local binders and declarations should usually use `Name`
-- directly.
--
-- ResolvedAstPhase paths are kept intentionally simple: the resolver preserves the
-- written path as text and records only the FINAL symbol the whole path
-- resolved to (individual segments are no longer separately meaningful once
-- resolution has happened). Example -- `Data::Left` becomes:
--
--   firstPathSegmentText      = "Data"
--   remainingPathSegmentTexts = ["Left"]
--   resolvedPathTargetSymbolId = SymbolId for Left
--------------------------------------------------------------------------------

public export
record PathNode (phase : AstPhase) where
  constructor MkPathNode
  firstSegment      : PathSegment phase
  remainingSegments : List (PathSegment phase)

public export
record ResolvedPathNode where
  constructor MkResolvedPathNode
  firstPathSegmentText       : String
  remainingPathSegmentTexts  : List String
  resolvedPathTargetSymbolId : SymbolId

public export
PathFor : AstPhase -> Type
PathFor SurfaceAstPhase   = PathNode SurfaceAstPhase
PathFor CanonicalAstPhase = PathNode CanonicalAstPhase
PathFor ResolvedAstPhase  = ResolvedPathNode
PathFor TypedAstPhase     = ResolvedPathNode

public export
Path : AstPhase -> Type
Path phase = AstNode phase (PathFor phase)

public export
SurfacePath : Type
SurfacePath = Path SurfaceAstPhase

public export
CanonicalPath : Type
CanonicalPath = Path CanonicalAstPhase

public export
ResolvedPath : Type
ResolvedPath = Path ResolvedAstPhase

public export
TypedPath : Type
TypedPath = Path TypedAstPhase

--------------------------------------------------------------------------------
-- Qualified names
--------------------------------------------------------------------------------
-- A QualifiedName is useful when later AST nodes want to distinguish:
--
--   optional qualifier path + final name/segment
--
-- This is often convenient for enum variants, qenum variants, associated
-- functions, and imported names.
--
-- Examples:
--
--   x
--     qualifierPath = Nothing
--     finalSegment  = x
--
--   Data::Left
--     qualifierPath = Just Data
--     finalSegment  = Left
--
--   Person::new
--     qualifierPath = Just Person
--     finalSegment  = new
--
-- This is still unresolved. `Person::new` is not known to be a method here,
-- and `Data::Left` is not known to be an enum/qenum variant here.
--------------------------------------------------------------------------------

public export
record QualifiedNameNode (phase : AstPhase) where
  constructor MkQualifiedNameNode
  qualifierPath : Maybe (Path phase)
  finalName     : Name phase

public export
QualifiedName : AstPhase -> Type
QualifiedName phase = AstNode phase (QualifiedNameNode phase)

public export
SurfaceQualifiedName : Type
SurfaceQualifiedName = QualifiedName SurfaceAstPhase

public export
CanonicalQualifiedName : Type
CanonicalQualifiedName = QualifiedName CanonicalAstPhase

public export
ResolvedQualifiedName : Type
ResolvedQualifiedName = QualifiedName ResolvedAstPhase

public export
TypedQualifiedName : Type
TypedQualifiedName = QualifiedName TypedAstPhase

module Frontend.ASTPhases

import Frontend.ASTData
import Frontend.Source

%default total

--------------------------------------------------------------------------------
-- Phase-specific AST wrappers
--------------------------------------------------------------------------------

public export
data AstPhase     -- The four phases of processing the AST, each with its own metadata.
  = SurfaceAstPhase       -- parser output
  | CanonicalAstPhase     -- desugaring output
  | ResolvedAstPhase      -- name and scope resolution output
  | TypedAstPhase         -- type checking output

public export
record ProvenanceMetadata where
  constructor MkProvenanceMetadata
  provenance : NodeProvenance

public export
MetadataFor : AstPhase -> Type
MetadataFor SurfaceAstPhase   = ()
MetadataFor CanonicalAstPhase = ProvenanceMetadata
MetadataFor ResolvedAstPhase  = ProvenanceMetadata
MetadataFor TypedAstPhase     = ProvenanceMetadata

public export
record AstNode (phase : AstPhase) a where
  constructor MkAstNode
  astInfo   : AstInfo
  metadata  : MetadataFor phase
  nodeValue : a

--------------------------------------------------------------------------------
-- Name aliases for the four phases
--------------------------------------------------------------------------------

public export
SurfaceAstNode : Type -> Type
SurfaceAstNode = AstNode SurfaceAstPhase

public export
CanonicalAstNode : Type -> Type
CanonicalAstNode = AstNode CanonicalAstPhase

public export
ResolvedAstNode : Type -> Type
ResolvedAstNode = AstNode ResolvedAstPhase

public export
TypedAstNode : Type -> Type
TypedAstNode = AstNode TypedAstPhase

--------------------------------------------------------------------------------
-- Smart constructors for the four phases
--------------------------------------------------------------------------------

public export
surfaceAstNode : AstInfo -> a -> SurfaceAstNode a
surfaceAstNode astInfo value =
  MkAstNode astInfo () value

public export
canonicalAstNode : AstInfo -> NodeProvenance -> a -> CanonicalAstNode a
canonicalAstNode astInfo origin value =
  MkAstNode astInfo (MkProvenanceMetadata origin) value

public export
resolvedAstNode : AstInfo -> NodeProvenance -> a -> ResolvedAstNode a
resolvedAstNode astInfo origin value =
  MkAstNode astInfo (MkProvenanceMetadata origin) value

public export
typedAstNode : AstInfo -> NodeProvenance -> a -> TypedAstNode a
typedAstNode astInfo origin value =
  MkAstNode astInfo (MkProvenanceMetadata origin) value

--------------------------------------------------------------------------------
-- Show instance: print the payload only, skip the bookkeeping
--------------------------------------------------------------------------------

public export
Show a => Show (AstNode phase a) where
  show (MkAstNode _ _ value) = show value

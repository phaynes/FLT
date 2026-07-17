import FLTMethodology.Probes.ClassFieldCharacterBoundary
import FLT.DedekindDomain.FiniteAdeleRing.LocalUnits

/-!
# Class-field idele topology boundary probe

This methodology-only file checks the exact multiplicative maps needed to place a finite local
uniformiser in the full idele group. It also checks that the transparent idele-class quotient name
inherits the expected group and topology instances.

It does not state connected-component, discreteness, profiniteness, reciprocity, globalization, or
automorphy theorems.
-/

open NumberField

namespace FLT.PotentialModularity.ClassField

variable (K : Type*) [Field K] [NumberField K]

/-- Embed the multiplicative monoid of finite adeles into the full adele monoid by putting `1` at
every infinite place. This is intentionally a monoid homomorphism, not a ring homomorphism. -/
noncomputable def finiteAdeleToAdele :
    IsDedekindDomain.FiniteAdeleRing (𝓞 K) K →* AdeleRing (𝓞 K) K :=
  MonoidHom.inr (InfiniteAdeleRing K) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)

/-- The induced map from finite ideles to full ideles. -/
noncomputable def finiteIdeleEmbedding :
    (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)ˣ →* (AdeleRing (𝓞 K) K)ˣ :=
  Units.map (finiteAdeleToAdele K)

/-- A chosen full idele which is a uniformiser at `v`, one at every other finite place, and one at
every infinite place. -/
noncomputable def localUniformiserIdele
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    [DecidableEq (IsDedekindDomain.HeightOneSpectrum (𝓞 K))] :
    (AdeleRing (𝓞 K) K)ˣ :=
  finiteIdeleEmbedding K (IsDedekindDomain.FiniteAdeleRing.localUniformiserUnit K v)

#synth CommGroup (IdeleClassGroup K)
#synth TopologicalSpace (IdeleClassGroup K)
#synth IsTopologicalGroup (IdeleClassGroup K)

end FLT.PotentialModularity.ClassField

#print axioms FLT.PotentialModularity.ClassField.finiteAdeleToAdele
#print axioms FLT.PotentialModularity.ClassField.finiteIdeleEmbedding
#print axioms FLT.PotentialModularity.ClassField.localUniformiserIdele

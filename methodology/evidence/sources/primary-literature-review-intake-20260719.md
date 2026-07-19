# Primary-literature review intake, 2026-07-19

## Decision

The supplied *Primary Literature Review for the Formalization of Fermat's Last Theorem*
is useful as a research-routing artefact. It is not a primary mathematical source and it
does not authorize any proof-obligation, source-design, or kernel-status promotion.

- Input SHA-256: `2cad77ad12bf4d48f588a529c6d0190d54d44a8885e1d1d70eaa66a82be1aa4a`
- Input size: 27,990 bytes
- Trusted FLT base: `1f6d11caee718028bf783c968511d34865ffd9f0`
- Adjudication scope: nine packets (`A1`--`A6`, `B1`--`B3`)
- Programme effect: additive evidence and design guidance only
- Lean effect: no `.lean` declaration added, changed, or promoted

The machine-readable adjudication is
`methodology/control/literature-assurance-delta-20260719.ndjson`. Lean-facing design
consequences are in
`methodology/source-design/literature-assisted-proof-design-20260719.md`.

## Primary bytes inspected

The following source files were obtained from the URLs proposed by the review or from
an author/institutional host. The bytes are retained only in the ignored build cache.

| Source | Inspected locator | SHA-256 | Result |
|---|---|---|---|
| Wiles (1995) | Theorems 0.1--0.2, printed pp. 445--447 | `69b968590df204c59702ee9ffcc857d8ee3cf683146c04133ff098c27bc2b831` | The review attributes the lifting conclusion to the wrong theorem. Theorem 0.1 constructs the Galois representation attached to an eigenform; Theorem 0.2 is the introductory lifting theorem. |
| Taylor--Wiles (1995) | Theorem 1, printed p. 556; Theorem 2, printed p. 557 | `ee7cc77cd5b297d5dd8d915ff28f78ef8d9947c4f2819db4e1e4724f1bb3f911` | Theorem 1 says the minimal Hecke ring `T` is a complete intersection. Theorem 2 says `T_Q` is free over `O[Delta_Q]` with the specified rank. Neither theorem alone supplies the full deformation, local-condition, or patching provider graph. |
| Mazur (1989) | printed pp. 385--386 | `1ea14721a6365111abc44115d0f0adf1f890206d237b75883491f3746f2276b2` | The scan and introductory universal-deformation claim are genuine, but “Proposition 1, p. 385” is not a valid locator. The exact repository representability route remains SRC-015 pending a theorem-by-theorem audit. |
| Langlands (1980) | section 2; Theorem 11.1; Lemma 11.2; Propositions 11.4--11.5 | `6af3f53d0eb0e841548f43151f9cb79fd2e12ceac4ca909aefeb08d5462758ab` | The review's “Theorem 11.2” locator is incorrect. Lemma 11.2 is a local character identity in the quadratic case. The prime-degree global route is distributed across the section-2 assertions and the section-11 trace-formula results. |
| Jacquet--Langlands (1970) | section 16, especially Theorem 16.1, printed p. 262 | `ede21b1b303d3a398eb0b9057716c4b293bafe39eba118fd9b6a871eab6f2dcf` | This is relevant historical correspondence material, but the authors say the section-16 argument is only a formal sketch, analytical facts remain unverified, and Theorem 16.1 must remain conjectural. It cannot be used as proof authority for the repository transfer. |
| Moret--Bailly (1989), part II | Definition 1.2, printed p. 181; Theorem 1.3, printed p. 182 | `fcd52552f0d04f06c9c07301341581ac37f04ef84eb5867a596c560588ab5fdd` | The theorem gives an integral point for every incomplete Skolem datum. The review is right that the FLT-specific Galoisness, total reality, degree, avoidance, and curve assembly are separate derived obligations, but its page locator is one page early. |
| Barnet-Lamb--Geraghty--Harris--Taylor (2009) | Theorem A, printed pp. 1--2 | `cd8a9435c852390f67a47bc1a4a99dd164d8593af123ff7e1f77711319c976f2` | The URL labelled “Harris (2008)” resolves to *A family of Calabi--Yau varieties and potential automorphy II*. Theorem A has explicit prime-size, polarization, ordinary-regularity, image, and cohomology hypotheses. It is not the claimed isolated compatible-family/Brauer-descent theorem. |

The already inspected Serre (1987), Moret--Bailly (1989), Tate (1995), and
Voight (2021) records in `methodology/SOURCE-REGISTER.md` remain controlling where
they are stronger or more exact than the supplied review.

## Packet adjudication

| Packet | Existing obligations | Intake result | Safe enrichment |
|---|---|---|---|
| `A1` Taylor--Wiles chain | `FLT-DEF-FUNCTOR`, `FLT-HECKE-ACTION`, `FLT-TW-PRIMES`, `FLT-PATCHING`, `FLT-MLT-SOURCE`, `FLT-MLT` | Useful bytes and two exact Taylor--Wiles locators; Wiles and Mazur locators corrected | Split representability, local conditions, Hecke action, auxiliary-prime selection, freeness, and the final complete-intersection terminal. Do not treat any one cited theorem as the whole chain. |
| `A2` base change/Jacquet--Langlands | `FLT-CBASE`, `FLT-JL`, `FLT-INDUCED-MOD` | Langlands locator refuted; institutional Jacquet--Langlands bytes acquired; section-16 terminal explicitly conjectural | Separate forward cyclic base change, invariant-image/descent, induced automorphy, local component transport, and level-preserving quaternionic transfer; locate a later proved source for the last item. |
| `A3` tame residue kernel | `FLT-LOCAL-GALOIS`, `FLT-TAME-RESIDUE` | No primary *Local Fields* bytes or printed page were supplied; `J_v` is repository-specific | Require a definition-to-source translation for `J_v`, then prove `P_v <= J_v <= I_v` without assuming equality or strictness. |
| `A4` auxiliary field | `FLT-MORET-BAILLY`, `FLT-AUX-LOCAL-FIELD`, `FLT-AUX-CURVE`, `FLT-POTMOD` | Theorem 1.3 verified at p. 182; FLT-specific conclusions remain absent | Keep Skolem-point existence separate from total reality, Galois closure, even degree, joint disjointness, unramifiedness, and elliptic-curve assembly. |
| `A5` compatible family/descent | `FLT-BRAUER-FAMILY`, `FLT-FAMILY`, `FLT-LIFT`, `FLT-CHEBOTAREV`, `FLT-BRAUER-NESBITT`, `FLT-COMPAT-CONTRA` | Citation identity and theorem scope corrected; no exact compatible-family descent source added | Preserve the existing BLGGT/Khare--Wintenberger route and keep Brauer induction, positivity/integrality, stable lattices, semisimplification, and named-member recovery distinct. |
| `A6` Fontaine--Odlyzko/3-adic | `FLT-FONTAINE-ODLYZKO`, `FLT-MOD3`, `FLT-THREEADIC`, `FLT-HR-REDUCIBLE` | Fontaine metadata confirmed, theorem bytes and Proposition 1.5 not inspected; `e_2 = 9` remains `no_result` | Retain separate providers for finite-flat ramification bounds, projective-image/discriminant contradiction, oriented stable quotient, and the all-powers-of-3 trace lift. |
| `B1` Frey local properties | `FLT-FREY-HR` and Tate support nodes | Serre bytes already known; proposed early sections do not discharge the four concrete Frey fields | Build a four-row source matrix for determinant, ramification away from `2p`, the place 2, and finite flatness at `p`. |
| `B2` Tate/Weil | `FLT-TATE-FLAT`, `FLT-TATE-UNRAMIFIED`, `FLT-TATE-WEIL` | No Silverman bytes added. Existing Tate primary source is more exact for uniformization and the finite-flat sequence | Continue the source-faithful pairing, zero-pairing exclusion, specialization, and local/global action bridges already recorded. |
| `B3` quaternion relative index | `FLT-HIST-QUATERNION` | Voight (2017) Theorem 5.1 is an ideal-class/mass result, not the exact relative-index terminal | Retain the operator-authorized Voight (2021) synthesis and its explicit unsourced compact-open-to-order injection. |

## What this intake does not prove

It does not prove that the literature campaign has closed any mathematical obligation,
that a cited theorem matches the repository's current definitions, that an interface
sketch elaborates, or that the old proof loop is safe to restart. Each future source
promotion still requires primary bytes, an exact printed locator, a one-to-one
hypothesis map, a discriminating consumer and negative probe, an axiom audit, and
independent source-fidelity review.

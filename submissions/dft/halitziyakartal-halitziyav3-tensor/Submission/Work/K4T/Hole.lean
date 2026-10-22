import Submission.Work.K4T.Stmt
import Submission.Work.Mixed.HeadM1
import Submission.Work.BlockAccounting.Moment
-- changed for the tensor-power extension (26159999/10000000000); see Submission.lean

/-!
# Route B (K4-heads-fresh tensor power): the RAW certificate statement and the tensor engine statement

* `RawCertG α ρ σ`  the RAW P4-L-fresh certificate with `G ≥ 1` gauge copies (no pad, no split): a word `wd` on roles
  `ρ`, live roles `σ` (injective `e`), arrays of 73 axes, every live role ending at `blockMat (tz l)` of its OWN input
  (`MX.GLiveKernelM`), target ranks distributed as `G` copies of `rawTgtB`, block histogram `G` copies of `rawPaidB`.
* `hole_rawCertG`      **HOLE (FAST-WRITER H2)**: a RAW certificate with `G` copies exists (p3-port: rawCert's word for
  the S2979B instance, before the pad and the split).
* `hole_tensorEngineG` **HOLE (FAST-WRITER H3)**: a RAW certificate with `G` copies gives the engine statement at the
  seam exponent `1 - 2615999999/10^12` (tensor agent: `TensorEng.k4f_engine_of_raw` for `G` copies: the 2730-fold
  tensor power completed to `14^2730` and split at `13^2730`, rate point `1 - 327/125000`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OAI
namespace PowerSaving
namespace PB
namespace K4T
open Binary Matrix Finset GF MX RAM

noncomputable section

/-- the RAW unit's paid blocks `(rank, count)` (= the tensor agent's `TensorProto.K4F.PK4F`). -/
def rawPaidB : List (ℕ × ℕ) :=
  [(1, 22005), (2, 6354), (3, 2088), (4, 972), (5, 162), (8, 744), (16, 448), (32, 224)]

/-- the RAW unit's live targets `(rank, count)` (= the tensor agent's `TensorProto.K4F.TK4F`). -/
def rawTgtB : List (ℕ × ℕ) :=
  [(4, 234), (5, 18), (6, 144), (7, 468), (8, 891), (9, 1917), (25, 448), (41, 224), (73, 224)]

/-- **The RAW P4-L-fresh certificate with `G` copies** on given types. -/
def RawCertG (α ρ σ : Type) [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ] [Fintype σ]
    [DecidableEq σ] : Prop :=
  ∃ (e : σ → ρ) (tr : σ → ℕ) (tz : ∀ l, Fin (tr l) → Space α) (wd : GWord α ρ) (G : ℕ),
    Function.Injective e ∧ (∀ l, LinearIndependent F (tz l)) ∧ wd.Proper (Fintype.card α) ∧
    MX.GLiveKernelM e (fun l => blockMat (tz l)) wd ∧
    1 ≤ G ∧ Fintype.card α = 73 ∧
    (∀ r, (Finset.univ.filter fun l => tr l = r).card = G * BlockAccounting.histFn rawTgtB r) ∧
    (∀ r, wd.hist r = G * BlockAccounting.histFn rawPaidB r)

end
end K4T
end PB
end PowerSaving
end OAI

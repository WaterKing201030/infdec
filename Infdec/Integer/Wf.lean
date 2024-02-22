import Infdec.Integer.Add

namespace wkmath
namespace int
def PosLt(x y:int):=
  Zero ≤ x ∧ x < y

theorem PosLt.acc(x:int):Acc PosLt x:=by{
  match x with
  | ⟨x', true⟩ => {
    apply Acc.intro
    intro _ h
    rw[PosLt] at h
    have h:=lt_of_le_of_lt h.left h.right
    simp[lt] at h
    exact h.elim
  }
  | ⟨x',false⟩ => {
    apply Acc.intro
    intro y h
    rw[PosLt] at h
    match y with
    | ⟨y', true⟩ => {
      apply Acc.intro
      intro z h''
      rw[PosLt] at h''
      have h'':=lt_of_le_of_lt h''.left h''.right
      rw[Zero] at h''
      simp[lt] at h''
    }
    | ⟨y', false⟩ => {
      simp[Zero, lt] at h
      have : y' < x' := h.right
      exact acc _
    }
  }
}
termination_by _ => x.digits

@[inline] instance PosLt.wf:WellFounded PosLt:=
  WellFounded.intro acc

end int
end wkmath

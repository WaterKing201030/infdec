import Infdec.Digits.Cycle

namespace wkmath
inductive digitsArr where
  | nil
  | cons(_:digitsArr)(_:Digits)

notation:1025 " δ " => digitsArr.nil
infixl:67 " :: " => digitsArr.cons

namespace Digits

def slice(x:Digits){r:Digits}(h:r ≠ ε):digitsArr:=
  if h'':x ≤L r then
    δ::x
  else
    have : (cutTails x r) <L x:=by{
      match x, r with
      | ε, _::_ => simp[len.le] at h''
      | _::_, _::_ => {
        rw[len.le] at h''
        rw[cutTails]
        exact len.lt_of_le_of_lt (cutTails_len_le _ _) (len.lt_cons _ _)
      }
    }
    (slice (cutTails x r) h)::(getTails x r)
termination_by' {
  rel:=λ x y => x.fst <L y.fst
  wf:=InvImage.wf (λ x:(_:Digits) ×' _ => x.fst) len.lt.wf
}

def preslice(x:Digits){r:Digits}(h:r ≠ ε):digitsArr:=
  if h':x ≤L r then
    δ
  else
    have : (cutTails x r) <L x:=by{
      match x, r with
      | ε, _::_ => simp[len.le] at h'
      | _::_, _::_ => {
        rw[len.le] at h'
        rw[cutTails]
        exact len.lt_of_le_of_lt (cutTails_len_le _ _) (len.lt_cons _ _)
      }
    }
    (preslice (cutTails x r) h)::(cutTails x r)
termination_by' {
  rel:=λ x y => x.fst <L y.fst
  wf:=InvImage.wf (λ x:(_:Digits) ×' _ => x.fst) len.lt.wf
}
end Digits

end wkmath

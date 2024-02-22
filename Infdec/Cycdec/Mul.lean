import Infdec.Cycdec.Base
import Infdec.Cycdec.Rat

namespace wkmath

namespace cyc

def cycmul{x:Digits}(h:x ≠ ε)(y:Digits):Digits × Digits:=
  (((x * y).slice h).sum.cutTails x,((x * y).slice h).sum.getTails x)

def loopadd(x0 x1:Digits){y:Digits}(h:y ≠ ε):Digits × Digits:=
  if h':(x1.cutTails y).isZero then
    (x0, x1.getTails y)
  else
    have :(x1.slice h).sum < x1:=Digits.slice_cutTails_not_zero_sum_lt h h'
    loopadd (x0 + (x1.preslice h).sum) (x1.slice h).sum h
termination_by' {
  rel:=λ x y => x.snd.fst < y.snd.fst
  wf:=InvImage.wf (λ (x:(_:Digits) ×' (_:Digits) ×' _) => x.snd.fst) Digits.nat.lt.wf
}

theorem loopadd_snd_len_le_thd(x0 x1:Digits){y:Digits}(h:y ≠ ε):(loopadd x0 x1 h).snd ≤L y:=by{
  rw[loopadd]
  cases Decidable.em (x1.cutTails y).isZero with
  | inl h' => {
    simp[h']
    exact Digits.getTails_len_le _ _
  }
  | inr h' => {
    simp[h']
    have : (x1.slice h).sum < x1:=Digits.slice_cutTails_not_zero_sum_lt h h'
    exact loopadd_snd_len_le_thd _ _ h
  }
}
termination_by' {
  rel:=λ x y => x.snd.fst < y.snd.fst
  wf:=InvImage.wf (λ (x:(_:Digits) ×' (_:Digits) ×' _) => x.snd.fst) Digits.nat.lt.wf
}

def mul(x:cyc)(y:Digits):cyc:=
  ⟨(loopadd (x.pre * y) (x.post * y) x.inv).fst, Digits.padheadzero (loopadd_snd_len_le_thd (x.pre * y) (x.post * y) x.inv), x.exp, (Digits.len.ne_of_eq_of_ne (Digits.padheadzero_len_eq (loopadd_snd_len_le_thd (x.pre * y) (x.post * y) x.inv)) (Digits.len.ne.intro (λ h:x.post =L ε => x.inv (Digits.len.ε_unique h)))).to_strict_ne⟩

end cyc
end wkmath

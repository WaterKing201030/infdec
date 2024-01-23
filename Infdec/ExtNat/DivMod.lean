import Infdec.ExtNat.Sub

namespace wkmath
namespace Digits
/-
theorem div_termination{x y:Digits}(h':¬x < y)(h:¬y.isZero):(x - y) < x:=by{
  rw[←nat.le_iff_not_gt] at h'
  cases h'.to_eq_or_lt with
  | inl h' => exact nat.sub_not_zero_lt (nat_eq_not_zero_isnot_zero h h') h
  | inr h' => exact nat.sub_not_zero_lt (nat.lt_not_zero h') h
}

def floordiv(x:Digits){y:Digits}(h:¬y.isZero):Digits:=
  if h':x < y then
    ε
  else
    have := div_termination h' h
    (floordiv (x - y) h) + One
termination_by _ => x

def mod(x:Digits){y:Digits}(h:¬y.isZero):Digits:=
  if h':x < y then
    ε
  else
    have := div_termination h' h
    (floordiv (x - y) h) + One
termination_by _ => x
-/

def divmod''(x y:Digits):Digit × Digits:=
  if x < y then
    ((0), x)
  else if x < y + y then
    ((1), x - y)
  else
    ((2), x - y - y)

def divmod'(x0 x1 y r:Digits):Digits × Digits:=
  if h:x1=ε then
    (r::(divmod'' x0 y).fst, (divmod'' x0 y).snd)
  else
    have : (tails h).isTails x1:=by rw[isTails]; simp[h]
    divmod' ((divmod'' x0 y).snd::(head h)) (tails h) y (r::(divmod'' x0 y).fst)
termination_by' {
  rel:=λ x y => (isTails x.snd.fst y.snd.fst)
  wf:=isTails.wf.psigma_fst.psigma_snd
}

def divmod(x y:Digits):Digits × Digits:=
  divmod' ε x y ε

def floordiv(x y:Digits):Digits:=
  (divmod x y).fst

def mod(x y:Digits):Digits:=
  (divmod x y).snd

infixl:70 " // " => floordiv
infixl:70 " % " => mod

end Digits
end wkmath

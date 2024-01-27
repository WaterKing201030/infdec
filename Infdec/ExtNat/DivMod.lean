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

/-
  mod one
  div one
  div mul add mod
  mul div cancel
 -/

def toNegOne:Digits → Digits
  | ε => ε
  | x::_ => (x.toNegOne)::(2)

theorem toNegOne_eq_of_len_eq{x y:Digits}(h:x =L y):x.toNegOne = y.toNegOne:=by{
  match x, y with
  | ε, ε => simp
  | _::_, _::_ => {
    simp[toNegOne]
    simp[len.eq] at h
    exact toNegOne_eq_of_len_eq h
  }
}

theorem head_append_toNegOne_eq_toNegOne_cons_Tail(x:Digits):(ε::(2))++x.toNegOne=x.toNegOne::(2):=by{
  induction x with
  | nil => simp[toNegOne]
  | cons xs xd ih => rw[toNegOne, append, ih]
}

theorem divmod''_zero(x:Digits){y:Digits}(h:y.isZero):divmod'' x y = ((2), x):=by{
  rw[divmod'']
  have h':(y + y).isZero:=nat_eq_zero_isZero' (nat.add_zero h) h
  simp[nat.not_lt_zero _ h]
  simp[nat.not_lt_zero _ h']
  repeat rw[sub_zero_eq h]
}

theorem not_ε_divmod'_zero'{x y:Digits}(hx:x≠ε)(hy:y.isZero)(z r:Digits):divmod' z x y r=divmod' (z::(head hx)) (tails hx) y (r::(2)):=by{
  rw[divmod']
  simp[hx]
  simp[divmod''_zero z hy]
}

theorem divmod'_zero(z x:Digits){y:Digits}(h:y.isZero)(r:Digits):divmod' z x y r=(r++(x.toNegOne)::(2), z++x)
:=by{
  have h:∀(z r:Digits), divmod' z x y r=(r++(x.toNegOne)::(2), z++x):=by{
    induction x using tails.recursion with
    | base => {
      intro z r
      rw[divmod']
      simp
      simp[divmod''_zero _ h]
      simp[toNegOne, append]
    }
    | ind x hx ih => {
      have hx':=eq_head_append_tails hx
      intro z r
      rw[divmod']
      simp[hx]
      simp[divmod''_zero _ h]
      rw[ih _ _]
      simp
      apply And.intro
      . {
        rw[←append_tail, append.assoc]
        have h:(ε :: (2)) ++ ((tails hx).toNegOne :: (2))=x.toNegOne::(2):=by{
          simp[append]
          rw[head_append_toNegOne_eq_toNegOne_cons_Tail]
          match x with
          | xs::xd => {
            rw[toNegOne_eq_of_len_eq (tails_len_eq_heads xs xd)]
            rw[toNegOne]
          }
        }
        rw[h]
      }
      . {
        rw[←append_tail, append.assoc, eq_head_append_tails]
      }
    }
  }
  exact h z r
}

theorem divmod_zero(x:Digits){y:Digits}(h:y.isZero):divmod x y = ((x.toNegOne)::(2), x):=by{
  rw[divmod]
  rw[divmod'_zero _ _ h]
  simp
}

theorem mod_zero(x:Digits){y:Digits}(h:y.isZero):x % y = x:=by{
  rw[mod]
  rw[divmod_zero _ h]
}

theorem floordiv_zero(x:Digits){y:Digits}(h:y.isZero):x // y = (x.toNegOne)::(2):=by{
  rw[floordiv]
  rw[divmod_zero _ h]
}

end Digits
end wkmath

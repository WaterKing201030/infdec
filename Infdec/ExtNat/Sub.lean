import Infdec.Nat

namespace wkmath
namespace Digits
def sub(x y:Digits):Digits:=
  if x < y then ε else half_sub x y

infixl:65 " - " => sub

def std_sub(x y:Digits):Digits:=
  (x - y).toStdNat

infixl:65 " -ₛ " => std_sub

theorem nat.sub_add_cancel{x y:Digits}(h:y ≤ x):x - y + y =N x:=by{
  rw[sub]
  simp[h.to_not_gt]
  exact le_half_sub_add_cancel h
}

theorem nat.add_sub_cancel(x y:Digits):x + y - y =N x:=
  nat.add_right_cancel (sub_add_cancel (nat.add_left_le x y)) (nat.eq.refl y)

theorem nat.sub_le(x y:Digits):x - y ≤ x:=by{
  cases le_or_gt y x with
  | inl h => {
    exact add_left_le_of_le (le_of_eq_of_le (sub_add_cancel h) (add_right_le x y))
  }
  | inr h => {
    simp[sub,h]
    exact nat.ε_le _
  }
}

theorem sub_zero_eq{x y:Digits}(h:y.isZero):x - y = x:=by{
  simp[sub, (nat.zero_le x h).to_not_gt]
  rw[half_sub_zero _ h]
}

theorem nat.sub_zero_nat_eq(x:Digits){y:Digits}(h:y.isZero):x - y =N x:=by{
  rw[sub_zero_eq h]
  exact nat.eq.refl _
}

theorem nat.sub_not_zero_lt{x y:Digits}(hx:¬x.isZero)(hy:¬y.isZero):x - y < x:=by{
  cases le_or_gt y x with
  | inl h => {
    cases (sub_le x y).to_eq_or_lt with
    | inl h' => {
      have h':=eq_of_eq_add_eq h' (eq.refl y)
      have h':=(sub_add_cancel h).symm.trans h'
      exact ((add_right_not_zero_lt x hy).to_ne.elim h').elim
    }
    | inr h' => exact h'
  }
  | inr h => {
    simp[sub,h]
    exact nat.ε_lt_notzero hx
  }
}

end Digits
end wkmath

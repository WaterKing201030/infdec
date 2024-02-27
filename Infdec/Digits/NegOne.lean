import Infdec.Digits.Tails

namespace wkmath
namespace Digits
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

theorem not_ε_toNegOne_not_zero{x:Digits}(h:x≠ε):¬x.toNegOne.isZero:=by{
  match x with | x'::_ => match x' with
  | ε => simp[toNegOne]
  | _::_ => simp[toNegOne, isZero]
}

theorem not_ε_toNegOne_not_ε{x:Digits}:x ≠ ε ↔ x.toNegOne ≠ ε:=by{
  apply Iff.intro
  . exact λ _ => match x with | _::_ => by simp[toNegOne]
  . exact λ h => match x with | ε => by simp[toNegOne] at h | _::_ => by simp
}

theorem toNegOne_toZero_eq_toZero(x:Digits):x.toNegOne.toZero = x.toZero:=by{
  induction x with
  | nil => simp
  | cons _ _ ih => simp[toZero, toNegOne]; exact ih
}

theorem toZero_toNegOne_eq_toNegOne(x:Digits):x.toZero.toNegOne = x.toNegOne:=by{
  induction x with
  | nil => simp
  | cons _ _ ih => simp[toZero, toNegOne]; exact ih
}

theorem append_toNegOne_eq_toNegOne_append(x y:Digits):(x ++ y).toNegOne = x.toNegOne ++ y.toNegOne:=by{
  induction y with
  | nil => simp[toNegOne]
  | cons _ _ ih => simp[toNegOne, append]; exact ih
}
end Digits
end wkmath

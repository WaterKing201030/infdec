import Infdec.Digits.Append

/-
Things needed for Representation
- Equiv -> len.eq
- Map -> toZero
- Represent -> isZero
- map_eq_of_equiv
- map_equiv
- map_is_represent
- is_represent_map_unchange
-/

namespace wkmath
namespace Digits

def toZero:Digits → Digits
  | ε => ε
  | x::_ => x.toZero::(0)

def isZero:Digits → Prop
  | ε => True
  | x::d => x.isZero ∧ d=(0)

@[inline] instance isZero.instDecidable{x:Digits}:Decidable (x.isZero):=
  match x with
  | ε => by simp[isZero]; exact instDecidableTrue
  | xs::xd => by
    simp[isZero]
    have : Decidable (xs.isZero) := instDecidable
    exact instDecidableAnd

theorem toZero_eq_of_len_eq{x y:Digits}(h:x =L y):x.toZero = y.toZero:=by{
  match x, y with
  | _, ε => have h:=len.ε_unique h; rw[h]
  | _::_, _::_ => simp[len.eq] at h; simp[toZero]; exact toZero_eq_of_len_eq h
}

theorem toZero_len_eq(x:Digits):x.toZero =L x:=by{
  induction x with
  | nil => simp
  | cons xs xd ih => simp[toZero,len.eq]; exact ih
}

theorem len_eq_of_toZero_eq{x y:Digits}(h:x.toZero = y.toZero):x =L y:=
  (toZero_len_eq x).symm.trans ((len.eq.from_strict_eq h).trans (toZero_len_eq y))

theorem len_eq_iff_toZero_eq{x y:Digits}:x =L y ↔ x.toZero = y.toZero :=
  Iff.intro toZero_eq_of_len_eq len_eq_of_toZero_eq

theorem toZero.idemp(x:Digits):x.toZero.toZero=x.toZero:=
  toZero_eq_of_len_eq (toZero_len_eq _)

theorem toZero_isZero(x:Digits):x.toZero.isZero:=by{
  induction x with
  | nil => simp[toZero,isZero]
  | cons xs xd ih => simp[toZero,isZero]; exact ih
}

theorem zero_toZero_eq{x:Digits}(h:x.isZero):x.toZero = x:=by{
  induction x with
  | nil => simp
  | cons xs xd ih => {
    simp[isZero] at h
    have ih:=ih h.left
    simp[toZero]
    exact And.intro ih (h.right.symm)
  }
}

theorem zero_append_zero_isZero{x y:Digits}(hx:x.isZero)(hy:y.isZero):(x:+y).isZero:=by{
  induction y with
  | nil => simp[hx]
  | cons ys yd ih => {
      simp[isZero] at *
      exact And.intro (ih hy.left) (hy.right)
  }
}

theorem zero_double_isZero{x:Digits}(h:x.isZero):x.double.isZero:=
  zero_append_zero_isZero h h

theorem zero_triple_isZero{x:Digits}(h:x.isZero):x.triple.isZero:=
  zero_append_zero_isZero (zero_double_isZero h) h

theorem ε_isZero:(ε).isZero:=by simp[isZero]

end Digits
end wkmath

import Infdec.Digits.Append
import Infdec.Base

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

theorem zero_append_zero_isZero{x y:Digits}(hx:x.isZero)(hy:y.isZero):(x++y).isZero:=by{
  induction y with
  | nil => simp[hx]
  | cons ys yd ih => {
      simp[isZero] at *
      exact And.intro (ih hy.left) (hy.right)
  }
}

theorem not_zero_append_isNotZero{x y:Digits}(hx:¬x.isZero):¬(x++y).isZero:=by{
  induction y with
  | nil => simp; exact hx
  | cons y' d ih => {
    simp[append, isZero]
    match d with
    | (0) => simp[ih]
    | (1) | (2) => simp
  }
}

theorem append_not_zero_isNotZero{x y:Digits}(hy:¬y.isZero):¬(x++y).isZero:=by{
  induction y with
  | nil => contradiction
  | cons y' d ih => {
    rw[isZero] at hy
    rw[de_morgan_not_and] at hy
    match d with
    | (0) => {
      simp at hy
      simp[ih hy, append, isZero]
    }
    | (1) | (2) => simp[append, isZero]
  }
}

theorem zero_double_isZero{x:Digits}(h:x.isZero):x.double.isZero:=
  zero_append_zero_isZero h h

theorem zero_triple_isZero{x:Digits}(h:x.isZero):x.triple.isZero:=
  zero_append_zero_isZero (zero_double_isZero h) h

theorem ε_isZero:(ε).isZero:=by simp[isZero]

theorem isZero.len_unique{x y:Digits}(hx:x.isZero)(hy:y.isZero)(h:x =L y):x=y:=by{
  have hx:=zero_toZero_eq hx
  have hy:=zero_toZero_eq hy
  rw[←hx,←hy]
  exact toZero_eq_of_len_eq h
}

theorem zero_head_eq_zero_tail{x:Digits}(h:x.isZero):ε::(0)++x=x::(0):=by{
  induction x with
  | nil => simp
  | cons xs xd ih => {
    rw[isZero] at h
    rw[h.right]
    rw[append]
    simp
    exact ih h.left
  }
}

theorem zero_append_zero_comm{x y:Digits}(hx:x.isZero)(hy:y.isZero):x ++ y = y ++ x:=by{
  induction x generalizing y with
  | nil => simp
  | cons xs xd ih => {
    match y with
    | ε => simp
    | ys::yd => {
      have hx':=hx
      have hy':=hy
      rw[isZero] at hx hy
      rw[hx.right] at *
      rw[hy.right] at *
      simp at *
      rw[append, append]
      simp
      rw[←zero_head_eq_zero_tail hx]
      have tmp: (ε::(0)).isZero := by simp
      rw[←ih hx tmp, append.assoc, zero_head_eq_zero_tail hy]
      exact ih hx hy'
    }
  }
}

theorem double_zero_cons_zero_eq_double_zero_cons_two_zero{x:Digits}(h:x.isZero):(x::(0)).double = (x.double::(0))::(0):=by{
  induction x with
  | nil => simp[double,append]
  | cons xs xd ih => {
    have h':=h
    simp[isZero] at h
    rw[h.right] at *
    have h':=ih h.left
    simp[double, append] at *
    rw[h']
    have tmp:((xs::(0))::(0)).isZero:=by simp[isZero]; exact h
    rw[zero_append_zero_comm tmp h]
    simp[append]
  }
}

theorem triple_zero_cons_zero_eq_triple_zero_cons_three_zero{x:Digits}(h:x.isZero):(x::(0)).triple=((x.triple::(0))::(0))::(0):=by{
  induction x with
  | nil => rfl
  | cons xs xd ih => {
    rw[isZero] at h
    rw[h.right] at *
    simp at h
    have ih:=ih h
    simp[triple, double, append] at *
    have tmp1:((xs::(0))::(0)).isZero:=by simp[isZero]; exact h
    have tmp2:((((xs :: (0)) :: (0) ++ xs) :: (0)) :: (0)).isZero:=by simp[isZero]; exact zero_append_zero_isZero tmp1 h
    rw[zero_append_zero_comm tmp2 h]
    simp[append]
    rw[←append.assoc]
    have tmp3{a b c:Digits}(h:a=b):a++c=b++c:=by rw[h]
    apply tmp3
    simp[append]
    have tmp4:(xs::(0)).isZero:=by simp[isZero]; exact h
    rw[zero_append_zero_comm tmp4 h]
    simp[append]
  }
}

end Digits
end wkmath

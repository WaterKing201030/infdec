import Infdec.Digits

/-
Things needed for Representation
- Equiv -> nat.eq
- Map -> toStdNat
- Represent -> isStdNat
- map_eq_of_equiv
- map_equiv
- map_is_represent
- is_represent_map_unchange
-/

namespace wkmath
namespace Digits
def nat.eq:Digits → Digits → Prop
  | ε, ε => True
  | ε, ds::d
  | ds::d, ε => (ds::d).isZero
  | xs::xd, ys::yd => eq xs ys ∧ xd = yd

notation:50 lhs:51 " =N " rhs:51 => nat.eq lhs rhs

@[inline] instance nat.eq.instDecidable{x y:Digits}:Decidable (x=Ny):=
  match x, y with
  | ε, ε => instDecidableTrue
  | ε, _::_
  | _::_, ε => isZero.instDecidable
  | x::_, y::_ =>
    have : Decidable (x =N y):=instDecidable
    instDecidableAnd

theorem zero_nat_eq_zero{x y:Digits}(hx:x.isZero)(hy:y.isZero):x =N y:=by{
  cases x with
  | nil => cases y with
    | nil => simp[nat.eq]
    | cons ys yd => simp[nat.eq];exact hy
  | cons xs xd => cases y with
    | nil => simp[nat.eq]; exact hx
    | cons ys yd => simp[nat.eq]; simp[isZero] at *;exact And.intro (zero_nat_eq_zero hx.left hy.left) (hx.right.trans hy.right.symm)
}

theorem nat.eq.refl(x:Digits):x =N x:=by{
  induction x with
  | nil => simp[eq]
  | cons xs xd ih => simp[eq]; exact ih
}

theorem nat.eq.symm{x y:Digits}(h:x =N y):y =N x:=by{
  match x, y with
  | ε, ε => simp[eq]
  | ε, ds::d
  | ds::d, ε => simp[eq] at *;exact h
  | xs::xd, ys::yd => simp[eq] at *; exact And.intro h.left.symm h.right.symm
}

theorem nat_eq_zero_isZero{x y:Digits}(h:x =N y)(hx:x.isZero):y.isZero:=by{
  match x, y with
  | _, ε => simp[isZero]
  | ε, _::_ => simp[nat.eq] at h; exact h
  | xs::xd, ys::yd => {
    rw[isZero] at hx
    rw[nat.eq] at h
    rw[hx.right] at h
    rw[←h.right]
    simp[isZero]
    exact nat_eq_zero_isZero h.left hx.left
  }
}

theorem nat_eq_zero_isZero'{x y:Digits}(h:x =N y)(hy:y.isZero):x.isZero:=
  nat_eq_zero_isZero h.symm hy

theorem nat.eq.trans{x y z:Digits}(h0:x =N y)(h1:y =N z):x =N z:=by{
  match x, y, z with
  | ε, _, _ => {
    exact zero_nat_eq_zero ε_isZero (nat_eq_zero_isZero h1 (nat_eq_zero_isZero h0 ε_isZero))
  }
  | _::_, ε, _ => {
    exact zero_nat_eq_zero (nat_eq_zero_isZero' h0 ε_isZero) (nat_eq_zero_isZero h1 ε_isZero)
  }
  | _::_, _::_, ε => {
    exact zero_nat_eq_zero (nat_eq_zero_isZero' h0 (nat_eq_zero_isZero' h1 ε_isZero)) ε_isZero
  }
  | _::_, _::_, _::_ => {
    simp[eq] at *
    exact And.intro (h0.left.trans h1.left) (h0.right.trans h1.right)
  }
}

theorem nat.eq.zero_head(x:Digits):ε::(0) :+ x =N x:=by{
  induction x with
  | nil => simp
  | cons x' d ih => {
    rw[append]
    rw[nat.eq]
    simp
    exact ih
  }
}

theorem nat.eq.zero_append{x:Digits}(h:x.isZero)(y:Digits):x:+y =N y:=by{
  induction x generalizing y with
  | nil => simp; exact eq.refl y
  | cons x' d ih => {
    rw[isZero] at h
    rw[←append_tail, append.assoc]
    have h0:=ih h.left (ε::d :+ y)
    have h1:=zero_head y
    rw[h.right] at h0
    rw[h.right]
    exact h0.trans h1
  }
}

theorem nat.quot_ind{P:Digits → Sort u}(h:∀(y x:Digits),x =N y→P x)(x:Digits):P x:=
  h x x (eq.refl x)

def toStdNat(x:Digits):Digits:=
  if h:x=nil then
    nil
  else
    let hd := head h
    let tl := tails h
    have : tl.isTails x:=by{
      rw[isTails]
      simp[h]
    }
    if hd = Digit.zero then
      tl.toStdNat
    else
      (ε::hd).append tl
termination_by _ => x

def isStdNat(x:Digits):Prop:=
  if h:x=nil then
    True
  else
    head h ≠ Digit.zero

theorem isStdNat.instDecidable{x:Digits}:Decidable (x.isStdNat):=
  match x with
  | ε => instDecidableTrue
  | _::_ => instDecidableNot

theorem toStdNat.zero_to_nil{x:Digits}(h:x.isZero):x.toStdNat=ε:=by{
  induction x using tails.recursion with
  | base => simp
  | ind x h' ih => {
    rw[toStdNat]
    simp[h']
    rw[head.zero_head]
    simp
    exact ih (tails.zero_tails h' h)
    exact h
  }
}

theorem stdNat_toStdNat_eq{x:Digits}(h:x.isStdNat):x.toStdNat = x:=by{
  cases x with
  | nil => simp[toStdNat]
  | cons xs xd => {
    rw[toStdNat]
    simp
    rw[isStdNat] at h
    simp at h
    simp[h]
    exact eq_head_append_tails (xs::xd).noConfusion
  }
}

theorem toStdNat_isStdNat(x:Digits):x.toStdNat.isStdNat:=by{
  rw[toStdNat,isStdNat]
  cases hx:x with
  | nil => {
    simp
  }
  | cons x' d => {
    simp
    cases Decidable.em (head (x'::d).noConfusion = (0)) with
    | inl h => {
      simp[h]
      rw[←isStdNat]
      have : (tails (x'::d).noConfusion).isTails x:=by {
        simp[hx]
        rw[isTails]
        simp
      }
      exact toStdNat_isStdNat (tails (x'::d).noConfusion)
    }
    | inr h => {
      simp[h]
      have h':=eq_head_append_tails (x'::d).noConfusion
      simp[h']
      exact h
    }
  }
}
termination_by _ => x

theorem isStdNat.stdNat_heads{x:Digits}{d:Digit}(h:(x::d).isStdNat):x.isStdNat:=by{
  cases Decidable.em (x=nil) with
  | inl h' => rw[h',isStdNat];simp
  | inr h' => {
    rw[isStdNat]
    simp[h']
    rw[isStdNat] at h
    simp at h
    have h'':head h' = head (x::d).noConfusion:=(head.cons_head h' d)
    intro hf
    apply h
    exact Eq.trans (Eq.symm h'') hf
  }
}

theorem isStdNat.unique{x y:Digits}(hx:x.isStdNat)(hy:y.isStdNat)(h:x =N y):x=y:=by{
  match x,y with
  | nil, nil => rfl
  | nil, cons y' yd => {
    rw[nat.eq] at h
    rw[isStdNat] at hy
    simp at hy
    have hc:=head.zero_head (y'::yd).noConfusion h
    contradiction
  }
  | cons x' xd, nil => {
    rw[nat.eq] at h
    rw[isStdNat] at hx
    simp at hx
    have hc:=head.zero_head (x'::xd).noConfusion h
    contradiction
  }
  | cons x' xd, cons y' yd => {
    simp
    rw[nat.eq] at h
    simp[h.right]
    have hx:=stdNat_heads hx
    have hy:=stdNat_heads hy
    exact unique hx hy h.left
  }
}

theorem toStdNat_nat_eq(x:Digits):x.toStdNat =N x:=by{
  induction x using tails.recursion with
  | base => rw[toStdNat]; simp
  | ind x' h ih => {
    rw[toStdNat]
    simp[h]
    rw[eq_head_append_tails]
    cases Decidable.em (head h=(0)) with
    | inl h' => {
      simp[h']
      apply nat.eq.trans ih
      have hx:=eq_head_append_tails h
      rw[h'] at hx
      have h'':=(nat.eq.zero_head (tails h)).symm
      apply nat.eq.trans h''
      rw[hx]
      exact nat.eq.refl x'
    }
    | inr h' => {
      simp[h']
      exact nat.eq.refl x'
    }
  }
}

theorem toStdNat_eq_of_nat_eq{x y:Digits}(h:x =N y):x.toStdNat = y.toStdNat:=by{
  apply isStdNat.unique (toStdNat_isStdNat x) (toStdNat_isStdNat y)
  exact (toStdNat_nat_eq x).trans (h.trans (toStdNat_nat_eq y).symm)
}

theorem toStdNat.idemp(x:Digits):x.toStdNat.toStdNat = x.toStdNat:=by{
  exact toStdNat_eq_of_nat_eq (toStdNat_nat_eq x)
}

theorem isStdNat.not_ε_cons{x:Digits}(hn:x≠ε)(h:x.isStdNat)(d:Digit):(x::d).isStdNat:=by{
  rw[isStdNat]
  simp
  rw[isStdNat] at h
  simp[hn] at h
  have h':=head.cons_head hn d
  rw[←h']
  exact h
}

end Digits
end wkmath

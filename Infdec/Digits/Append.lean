import Infdec.Digits.LenOrder

namespace wkmath
namespace Digits

def append:Digits → Digits → Digits
  | x, ε => x
  | x, y::d => (x.append y)::d

notation:65 lhs:66 " :+ " rhs:66 => append lhs rhs

section strict

@[simp] theorem append_ε(x:Digits):x :+ ε = x:=by simp[append]
@[simp] theorem ε_append(x:Digits):ε :+ x = x:=by{
  induction x with
  | nil => simp
  | cons xs xd ih => rw[append,ih]
}
theorem append_cons(x y:Digits)(d:Digit):x:+y::d = (x:+y)::d:=by simp[append]

theorem append_tail(x:Digits)(d:Digit):x :+ ε::d = x::d := by simp[append]

theorem append.ε_unique{x y:Digits}(h:x :+ y = ε):x=ε∧y=ε:=by{
  match x, y with
  | ε, ε => simp
  | _::_, ε => contradiction
}

theorem append_not_ε(x:Digits){y:Digits}(h:y≠ε):x :+ y ≠ ε :=by{
  intro h
  have h:=(append.ε_unique h).right
  contradiction
}

theorem not_ε_append{x:Digits}(h:x≠ε)(y:Digits):x :+ y ≠ ε := by{
  intro h
  have h:=(append.ε_unique h).left
  contradiction
}

theorem append.assoc(x y z:Digits):(x:+y):+z=x:+(y:+z):=by{
  induction z with
  | nil => simp
  | cons zs zd ih => simp[append]; exact ih
}

theorem append.right_cancel{x y z:Digits}(h:x :+ z = y :+ z):x = y:=by{
  induction z with
  | nil => simp at h; exact h
  | cons zs zd ih => simp[append] at h; exact ih h
}

theorem append.head_cancel{x y:Digits}{d:Digit}(h:ε::d :+ x = ε::d :+ y):x = y:=by{
  match x, y with
  | ε, ε => simp
  | ε, ys::_ => {
    simp[append] at h
    have h:=h.left.symm
    have h':=not_ε_append (ε::d).noConfusion ys
    contradiction
  }
  | xs::_, ε => {
    simp[append] at h
    have h:=h.left
    have h':=not_ε_append (ε::d).noConfusion xs
    contradiction
  }
  | _::_, _::_ => {
    simp[append] at h
    rw[h.right]
    simp
    exact head_cancel h.left
  }
}

theorem append.left_cancel{x y z:Digits}(h:x :+ y = x :+ z):y = z:=by{
  induction x generalizing y z with
  | nil => simp at h; exact h
  | cons xs xd ih => {
    rw[←append_tail xs xd,assoc,assoc] at h
    have h:=ih h
    exact head_cancel h
  }
}

end strict

section len
section eq
theorem append.len_eq_congr{x y z w:Digits}(h0:x =L z)(h1:y =L w):x:+y =L z:+w:=by{
  match y, w with
  | _, ε => {
    have h1:=len.ε_unique h1
    rw[h1]
    simp
    exact h0
  }
  | _::_, _::_ => {
    simp[len.eq] at *
    exact len_eq_congr h0 h1
  }
}

theorem head_len_eq_tail{x y:Digits}(h:x=Ly)(c d:Digit):ε::c:+x=Ly::d:=by{
  match x, y with
  | _, ε => {
    have h:=len.ε_unique h
    rw[h]
    simp[len.eq]
  }
  | _::_, _::_ => {
    simp[len.eq] at *
    exact head_len_eq_tail h _ _
  }
}

theorem append.len_eq_comm(x y:Digits):x:+y=Ly:+x:=by{
  induction x generalizing y with
  | nil => simp; exact len.eq.refl _
  | cons xs xd ih => {
    rw[←append_tail, assoc, append_tail]
    simp[append]
    have h:xs :+ (ε::xd :+ y) =L (xs :+ y)::xd:=by{
      rw[←append_tail (xs :+ y) xd]
      rw[assoc]
      rw[append_tail]
      exact len_eq_congr (len.eq.refl _) (head_len_eq_tail (len.eq.refl _) _ _)
    }
    apply h.trans
    rw[len.eq]
    exact ih _
  }
}

theorem append.len_eq_right_cancel{x y z w:Digits}(h0:x:+y=Lz:+w)(h1:y=Lw):x=Lz:=by{
  match y, w with
  | _, ε => {
    have h1:=len.ε_unique h1
    rw[h1] at h0
    simp at h0
    exact h0
  }
  | _::_, _::_ => {
    simp[len.eq] at *
    exact len_eq_right_cancel h0 h1
  }
}

theorem append.len_eq_left_cancel{x y z w:Digits}(h0:x:+y=Lz:+w)(h1:x=Lz):y=Lw:=
  len_eq_right_cancel ((len_eq_comm y x).trans (h0.trans (len_eq_comm z w))) h1
end eq
section le
theorem append.len_le_left_append(x y:Digits):x≤Ly:+x:=by{
  induction x with
  | nil => simp; exact len.ε_le _
  | cons xs xd ih => simp[len.le]; exact ih
}

theorem append.len_le_right_append(x y:Digits):x≤Lx:+y:=
  len.le_of_le_of_eq (len_le_left_append _ _) (len_eq_comm _ _)

theorem append.len_le_append_right_cancel{x y z:Digits}(h:x:+y≤Lz):x≤Lz:=by{
  induction y with
  | nil => simp at h; exact h
  | cons ys yd ih => {
    rw[append] at h
    have h:=(len.le_cons _ _).trans h
    exact ih h
  }
}

theorem append.len_le_append_left_cancel{x y z:Digits}(h:x:+y≤Lz):y≤Lz:=
  len_le_append_right_cancel (len.le_of_eq_of_le (len_eq_comm _ _) h)

theorem append.len_le_congr{x y z w:Digits}(h0:x ≤L z)(h1:y ≤L w):x :+ y ≤L z:+ w:=by{
  match y, w with
  | _, ε => {
    have h1:=len.le_ε_is_ε h1
    rw[h1]
    simp
    exact h0
  }
  | ε, _::_ => {
    simp
    exact h0.trans (len_le_right_append _ _)
  }
  | _::_, _::_ => simp[len.le] at *; exact len_le_congr h0 h1
}

theorem append.len_le_monotone_right_cancel{x y z w:Digits}(h0:x:+y≤Lz:+w)(h1:w≤Ly):x≤Lz:=by{
  match y, w with
  | ε, _ => {
    have h1:=len.le_ε_is_ε h1
    rw[h1] at h0
    simp at h0
    exact h0
  }
  | _::_, ε => {
    simp at h0
    exact len_le_append_right_cancel h0
  }
  | _::_, _::_ => {
    simp[append, len.le] at *
    exact len_le_monotone_right_cancel h0 h1
  }
}

theorem append.len_le_monotone_left_cancel{x y z w:Digits}(h0:x:+y≤Lz:+w)(h1:z≤Lx):y≤Lw:=
  len_le_monotone_right_cancel (len.le_of_eq_of_le (len_eq_comm _ _) (len.le_of_le_of_eq h0 (len_eq_comm _ _))) h1
end le
section lt
theorem append.len_lt_left_append_not_ε{y:Digits}(h:y≠ε)(x:Digits):x<Ly:+x:=by{
  induction x with
  | nil => simp; exact len.ε_lt_not_ε h
  | cons xs xd ih => simp[append,len.lt];exact ih
}
theorem append.len_lt_right_append_not_ε(x:Digits){y:Digits}(h:y≠ε):x<Lx:+y:=
  len.lt_of_lt_of_eq (len_lt_left_append_not_ε h _) (len_eq_comm _ _)

theorem append.len_lt_append_right_cancel{x y z:Digits}(h:x:+y <L z):x<Lz:=by{
  induction y with
  | nil => simp at h; exact h
  | cons ys yd ih => {
    rw[append] at h
    exact ih ((len.lt_cons _ _).trans h)
  }
}

theorem append.len_lt_append_left_cancel{x y z:Digits}(h:x:+y<Lz):y<Lz:=
  len_lt_append_right_cancel (len.lt_of_eq_of_lt (len_eq_comm _ _) h)

theorem append.len_lt_of_len_lt_append_len_le{x y z w:Digits}(h0:x <L z)(h1:y ≤L w):x:+y<Lz:+w:=by{
  have h2:=h0.to_le
  have h3:=len_le_congr h2 h1
  rw[len.lt_iff_le_and_ne]
  simp[h3]
  apply len.ne.intro
  intro h4
  have h4:=h4.symm.to_le
  have h0:=h0.to_not_ge
  apply h0
  exact len_le_monotone_right_cancel h4 h1
}

theorem append.len_lt_of_len_le_append_len_lt{x y z w:Digits}(h0:x≤Lz)(h1:y<Lw):x:+y<Lz:+w:=
  len.lt_of_eq_of_lt (len_eq_comm _ _) (len.lt_of_lt_of_eq (len_lt_of_len_lt_append_len_le h1 h0) (len_eq_comm _ _))

theorem append.len_lt_congr{x y z w}(h0:x<Lz)(h1:y<Lw):x:+y<Lz:+w:=
  len_lt_of_len_lt_append_len_le h0 h1.to_le

theorem append.len_lt_monotone_right_cancel{x y z w:Digits}(h0:x:+y<Lz:+w)(h1:w≤Ly):x<Lz:=by{
  match y, w with
  | ε, _ => {
    have h1:=len.le_ε_is_ε h1
    rw[h1] at h0
    simp at h0
    exact h0
  }
  | _::_, ε => {
    simp at h0
    exact len_lt_append_right_cancel h0
  }
  | _::_, _::_ => {
    simp[append, len.le, len.lt] at *
    exact len_lt_monotone_right_cancel h0 h1
  }
}

theorem append.len_lt_monotone_left_cancel{x y z w:Digits}(h0:x:+y<Lz:+w)(h1:z≤Lx):y<Lw:=
  len_lt_monotone_right_cancel (len.lt_of_eq_of_lt (len_eq_comm _ _) (len.lt_of_lt_of_eq h0 (len_eq_comm _ _))) h1
end lt
end len

theorem append.mid_double_cancel{x y z:Digits}(h:(y:+x):+y=(z:+x):+z):y=z:=by{
  match y, z with
  | ε, ε => simp
  | ε, zs::zd => {
    simp at h
    have h':x <L (zs :: zd :+ x) :+ zs :: zd:= (len_lt_left_append_not_ε (zs::zd).noConfusion _).trans (len_lt_right_append_not_ε _ (zs::zd).noConfusion)
    have h':=h'.to_ne.to_strict_ne
    contradiction
  }
  | ys::yd, ε => {
    simp at h
    have h':x <L (ys :: yd :+ x) :+ ys :: yd:= (len_lt_left_append_not_ε (ys::yd).noConfusion _).trans (len_lt_right_append_not_ε _ (ys::yd).noConfusion)
    have h':=h'.to_ne.to_strict_ne.symm
    contradiction
  }
  | ys::yd, zs::zd => {
    simp[append] at *
    simp[h.right]
    rw[h.right] at h
    have h:=h.left
    rw[←append_tail ys,←append_tail zs] at h
    rw[assoc ys _ x, assoc zs _ x] at h
    exact mid_double_cancel h
  }
}

theorem append.mid_triple_cancel{x y z w:Digits}(h:(((x:+z):+x):+w):+x=(((y:+z):+y):+w):+y):x=y:=by{
  match x, y with
  | ε, ε => simp
  | ε, ds::d => {
    simp at h
    have h0:z:+w <L (((ds :: d :+ z) :+ ds :: d) :+ w) :+ ds :: d:=by{
      rw[assoc]
      exact len_lt_congr ((len_lt_left_append_not_ε (ds::d).noConfusion _).trans (len_lt_right_append_not_ε _ (ds::d).noConfusion)) (len_lt_right_append_not_ε _ (ds::d).noConfusion)
    }
    have h0:=h0.to_ne.to_strict_ne
    contradiction
  }
  | ds::d, ε => {
    simp at h
    have h0:z:+w <L (((ds :: d :+ z) :+ ds :: d) :+ w) :+ ds :: d:=by{
      rw[assoc]
      exact len_lt_congr ((len_lt_left_append_not_ε (ds::d).noConfusion _).trans (len_lt_right_append_not_ε _ (ds::d).noConfusion)) (len_lt_right_append_not_ε _ (ds::d).noConfusion)
    }
    have h0:=h0.to_ne.to_strict_ne.symm
    contradiction
  }
  | xs::xd, ys::yd => {
    simp[append] at h
    simp[h.right] at *
    rw[←append_tail xs, ←append_tail] at h
    rw[←append_tail ys, ←append_tail (((ys :+ ε :: yd) :+ z) :+ ys)] at h
    rw[assoc _ _ z, assoc _ _ w] at h
    rw[assoc _ _ z, assoc _ _ w] at h
    exact mid_triple_cancel h
  }
}

def double(x:Digits):Digits:=
  x.append x

theorem double.cancel{x y:Digits}(h:x.double = y.double):x=y:=by{
  rw[double, double] at h
  rw[←append_ε x, ←append_ε y] at h
  rw[←append.assoc, ←append.assoc] at h
  rw[append_ε ((x:+ε):+x),append_ε ((y:+ε):+y)] at h
  exact append.mid_double_cancel h
}

def triple(x:Digits):Digits:=
  x.double.append x

theorem triple.cancel{x y:Digits}(h:x.triple = y.triple):x=y:=by{
  simp[triple,double] at h
  have h':(((x :+ ε) :+ x) :+ ε) :+ x = (((y :+ ε) :+ y) :+ ε) :+ y:=by simp; exact h
  exact append.mid_triple_cancel h'
}

end Digits
end wkmath

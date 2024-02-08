import Infdec.Integer

namespace wkmath
class cyc where
  pre:Digits
  post:Digits
  exp:int

namespace cyc
axiom eq:cyc → cyc → Prop
notation:50 lhs:51 " =C " rhs:51 => eq lhs rhs

axiom eq.refl':∀{x y:cyc}, x.pre =N y.pre → x.post = y.post → x.exp =I y.exp → x =C y
axiom eq.symm:∀{x y:cyc}, x =C y → y =C x
axiom eq.trans:∀{x y z:cyc}, x =C y → y =C z → x =C z
axiom eq.exp_move_right:∀{x:cyc},(h:x.pre ≠ ε) → x =C {pre:=x.pre::(Digits.head h), post:=(Digits.tails h)::(Digits.head h), exp:=x.exp - int.One}
axiom eq.cyc_min:∀{x:cyc},x =C {pre:=x.pre, post:=x.post.minCyc, exp:=x.exp}
/-再加一个可以找出最小循环节的算法-/

theorem eq.refl(x:cyc):x =C x:=
  refl' (Digits.nat.eq.refl _) rfl (int.eq.refl _)
theorem eq.symm_iff{x y:cyc}:x =C y ↔ y =C x:=
  Iff.intro symm symm
end cyc
end wkmath

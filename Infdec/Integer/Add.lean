import Infdec.Integer.Order

namespace wkmath
namespace int
def add:int → int → int
  | ⟨x0, true⟩, ⟨y0, true⟩ => ⟨x0 + y0, true⟩
  | ⟨x0, true⟩, ⟨y0, false⟩ => if y0 ≤ x0 then ⟨x0 - y0, true⟩ else ⟨y0 - x0, false⟩
  | ⟨x0, false⟩, ⟨y0, true⟩ => if y0 ≤ x0 then ⟨x0 - y0, false⟩ else ⟨y0 - x0, true⟩
  | ⟨x0, false⟩, ⟨y0, false⟩ => ⟨x0 + y0, false⟩

def add'(x y:int):int:=
  if x.negsign = y.negsign then
    ⟨x.digits + y.digits, x.negsign⟩
  else
    (if y.digits ≤ x.digits then ⟨x.digits - y.digits, x.negsign⟩ else ⟨y.digits - x.digits, y.negsign⟩)

theorem add_eq_add'{x y:int}:add x y = add' x y:=
  match x, y with
  | ⟨_, true⟩, ⟨_, true⟩
  | ⟨_, false⟩, ⟨_, false⟩
  | ⟨_, true⟩, ⟨_, false⟩
  | ⟨_, false⟩, ⟨_, true⟩ => rfl

infixl:65 " + " => add

def sub(x y:int):int:=
  x + (- y)

infixl:65 " - " => sub
end int
end wkmath

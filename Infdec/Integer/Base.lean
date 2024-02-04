import Infdec.ExtNat

namespace wkmath

class int where
  digits:Digits
  negsign:Bool

namespace int
def ofnat(x:Digits):int:=
  ⟨x,false⟩

def neg:int → int
  | ⟨x,false⟩ => ⟨x,true⟩
  | ⟨x,true⟩ => ⟨x,false⟩

prefix:75 "-"    => neg

def neg.inv{x:int}:-(-x) = x:=
  match x with | ⟨_,false⟩ | ⟨_, true⟩ => rfl

def isZero(x:int):=
  x.digits.isZero
end int

end wkmath

structure State where
  t : Float
  y : Float
deriving Repr

def eulerStep (f : Float → Float → Float) (dt : Float) (s : State) : State :=
  { t := s.t + dt
  , y := s.y + dt * f s.t s.y
  }

def eulerRec (f  : Float → Float → Float) (dt : Float) : Nat → State → List State
  | 0,     s => [s]
  | n+1,   s => let s' := eulerStep f dt s
                s :: eulerRec f dt n s'

def f (t y : Float) : Float :=
  y  -- y' = y

def sol : List State :=
  eulerRec f 0.1 100 { t := 0.0, y := 1.0 }

#eval sol.take 5

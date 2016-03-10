{-# LANGUAGE TypeOperators #-}
module HotelKey where

import Tip.Prelude
import qualified Prelude as P

{-
typedecl guest
typedecl key
typedecl room

type_synonym keycard = "key × key"
-}

type Guest   = Nat
type Key     = Nat
type Room    = Nat
type KeyCard = (Key,Key)

{-
record state =
owns :: "room ⇒ guest option"
currk :: "room ⇒ key"
issued :: "key set"
cards :: "guest ⇒ keycard set"
roomk :: "room ⇒ key"
isin :: "room ⇒ guest set"
safe :: "room ⇒ bool"
-}

data State = State
  { owns   :: Map (Maybe Guest)
  , currk  :: Map Key
  , issued :: Set
  , cards  :: Map Set2
  , roomk  :: Map Key
  , isin   :: Map Set
  , safe   :: Set
  }
 deriving ( P.Show )

{-  
inductive_set reach :: "state set" where
-}

type Domain = Nat

ind :: Room -> Domain -> Bool
Z   `ind` _   = True
S i `ind` Z   = False
S i `ind` S j = i `ind` j

inj :: Domain -> Map Nat -> Bool
inj Z       _          = True
inj (S _)   (Rest _)   = False
inj j@(S i) (Slot x m) = inj i m && upto j x m
 where
  upto Z     _ _          = True
  upto (S _) x (Rest y)   = not (x == y)
  upto (S i) x (Slot y m) = not (x == y) && upto i x m

data Reach
  = Init (Map Key)
  | CheckIn   Guest Room Key     Reach
  | EnterRoom Guest Room KeyCard Reach
  | ExitRoom  Guest Room         Reach
 deriving ( P.Show )

{-
init:
"inj initk ⟹
⦇owns = (λr. None), currk = initk, issued = range initk, cards = (λg. {}),
roomk = initk, isin = (λr. {}), safe = (λr. True)⦈ ∈ reach" |
-}

reach :: Domain -> Reach -> Maybe State
reach dom (Init initk) =
  if inj dom initk then
    Just State
    { owns   = cnst Nothing
    , currk  = initk
    , issued = range initk
    , cards  = cnst empty2
    , roomk  = initk
    , isin   = cnst empty
    , safe   = cnst True
    }
  else
    Nothing

{-
check_in:
"⟦s ∈ reach; k ∉ issued s⟧ ⟹
s⦇currk := (currk s)(r := k), issued := issued s ∪ {k},
 cards := (cards s)(g := cards s g ∪ {(currk s r, k)}),
 owns :=  (owns s)(r := Some g), safe := (safe s)(r := False)⦈ ∈ reach" |
-}

reach dom (CheckIn g r k q) =
  case reach dom q of
    Just s | r `ind` dom && not (issued s ! k) ->
      Just s
      { currk  = currk s != (r,k)
      , issued = add k (issued s)
      , cards  = cards s != (g, add2 (currk s ! r, k) (cards s ! g))
      , owns   = owns s != (r, Just g)
      , safe   = safe s != (r, False)
      }

    _ -> Nothing

{-
enter_room:
"⟦s ∈ reach; (k,k') ∈ cards s g; roomk s r ∈ {k,k'}⟧ ⟹
s⦇isin := (isin s)(r := isin s r ∪ {g}),
 roomk := (roomk s)(r := k'),
 safe := (safe s)(r := owns s r = Some g ∧ isin s r = {} (* ∧ k' = currk s r *)
                       ∨ safe s r)⦈ ∈ reach" |
-}

reach dom (EnterRoom g r (k,k') q) =
  case reach dom q of
    Just s | r `ind` dom && (cards s ! g) !! (k,k') && (rk == k || rk == k') ->
      Just s
      { isin  = isin s != (r, add g (isin s ! r))
      , roomk = roomk s != (r, k')
      , safe  = safe s != (r, ( ((owns s ! r) ==? Just g)
                             && (isin s ! r <=> empty)
                             -- && k' == currk s ! r
                              ) || safe s ! r)
      }
     where
      rk = roomk s ! r

    _ -> Nothing

{-
exit_room:
"⟦s ∈ reach; g ∈ isin s r⟧ ⟹ s⦇isin := (isin s)(r := isin s r - {g})⦈ ∈ reach"
-}

reach dom (ExitRoom g r q) =
  case reach dom q of
    Just s | r `ind` dom && (isin s ! r) ! g ->
      Just s
      { isin  = isin s != (r, rem g (isin s ! r))
      }

    _ -> Nothing

{-
theorem safe: "s ∈ reach ⟹ safe s r ⟹ g ∈ isin s r ⟹ owns s r = Some g"
-}

psafe :: Domain -> Room -> Guest -> Reach -> Bool
psafe dom r g q =
 case reach dom q of
    Just s | r `ind` dom && safe s ! r && (isin s ! r) ! g ->
      owns s ! r ==? Just g
    
    _ -> True

prop_safe0     r g q = psafe Z     r g q === True
prop_safe1     r g q = psafe (S Z) r g q === True
prop_safe2 dom r g q = psafe dom   r g q === True
prop_safe3     r g q = psafe (S (S (S Z))) r g q === True

-- LIBRARY --

data Map a
  = Rest a
  | Slot a (Map a)
 deriving ( P.Show )

(!) :: Map a -> Nat -> a
Rest x   ! _     = x
Slot x m ! Z     = x
Slot _ m ! (S i) = m ! i

(!=) :: Map a -> (Nat,a) -> Map a
m@(Rest x) != (Z,  y) = Slot y m
m@(Rest x) != (S i,y) = Slot x (m != (i,y))
Slot _ m   != (Z,  y) = Slot y m
Slot x m   != (S i,y) = Slot x (m != (i,y))

first :: Map a -> a
first (Rest x)   = x
first (Slot x _) = x

shift :: Map a -> Map a
shift m@(Rest x) = m
shift (Slot _ m) = m

type Set  = Map Bool
type Set2 = Map (Map Bool)

(<=>) :: Map Bool -> Map Bool -> Bool
Rest x   <=> Rest y   = x ==. y
Slot x p <=> Slot y q = (x ==. y) && (p <=> q)
Slot x p <=> Rest y   = (x ==. y) && (p <=> Rest y)
Rest x   <=> Slot y q = (x ==. y) && (Rest x <=> q)

cnst :: b -> Map b
cnst x = Rest x

empty :: Set
empty = Rest False

add, rem :: Nat -> Set -> Set
add x s = s != (x, True)
rem x s = s != (x, False)

range :: Map Nat -> Set
range (Rest x)   = add x empty
range (Slot x m) = add x (range m)

empty2 :: Set2
empty2 = Rest (Rest False)

add2 :: (Nat,Nat) -> Set2 -> Set2
add2 (x,y) s = s != (x, add y (s ! x))

(!!) :: Set2 -> (Nat,Nat) -> Bool
s !! (x,y) = (s ! x) ! y

-- Maybe

(==?) :: Maybe Nat -> Maybe Nat -> Bool
Nothing ==? Nothing = True
Just x  ==? Just y  = x == y
_       ==? _       = False

-- Bool

(==.) :: Bool -> Bool -> Bool
True  ==. y = y
False ==. x = not x


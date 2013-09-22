{-# LANGUAGE ScopedTypeVariables #-}

module Battle where
import Control.Monad
import Data.Array
import Data.Foldable (foldMap)
import Data.Functor
import qualified Data.List as L
import Data.Monoid
import System.Random
import Test.QuickCheck
import Text.Printf

{- TODO

 + QuickCheck
 + Maybe scores should just be (group, card-sum) tuples rather than a coded integer
 - I think some best-score code depends on avail being sorted by decreasing score
 - Actually avail doesn't really make sense as is, since transferring a card from
   the deck to a person's hand shouldn't affect it. But trying to compute a score
   should alway virtually play the card, removing it from avail.

-}

-- * Support

-- Probably super slow since we're splicing the list back together
-- every time we recurse.
-- | Return a random permutation of the given list.
shuffle :: (RandomGen r) => r -> [a] -> [a]
shuffle r [] = []
shuffle r xs =
    let (i, r') = randomR (0, length xs - 1) r
        (top, bot@(y:ys)) = splitAt i xs
    in y : shuffle r' (top ++ ys)

-- | Return the first Just value (unwrapped).
firstJust :: [Maybe a] -> a
firstJust xs = x where Just x = getFirst $ foldMap First xs

-- | True if the length of the given list is at least n.
lengthAtLeast :: (Num n, Eq n) => n -> [a] -> Bool
lengthAtLeast 0 _  = True
lengthAtLeast n [] = False
lengthAtLeast n (x:xs) = lengthAtLeast (n-1) xs

-- * Suits and ranks

data Suit = B | G | R | O | Y | P
            deriving (Eq, Ord, Enum, Show, Read)

type Rank = Int

-- | All valid suits.
suits = enumFrom B
-- | All valid ranks, best first.
ranks = reverse [1..10]

-- * Card

data Card = Card {
                  suit :: Suit,
                  rank :: Rank
                 }
          deriving (Eq, Read)
instance Show Card where
    show c = (show (suit c)) ++ (show (rank c))
instance Ord Card where
    compare x y | rank x <  rank y = LT
                | rank x >  rank y = GT
                | rank x == rank y = compare (suit x) (suit y)
mkCard s r = Card { suit = s, rank = r }

-- * CardGroup

data CardGroup = CardGroup {
                            group          :: [Card],
                            groupTimestamp :: Int -- ^ Tiebreaker when comparing groups.
                           }
               deriving (Show)
-- | An empty card group.
emptyGroup = CardGroup { group=[], groupTimestamp=0 }

-- * GroupType
-- | A category of three-card poker hand.
data GroupType = Random | Straight | Flush | ThreeOfAKind | StraightFlush
               deriving (Eq, Ord, Enum, Show, Read)

-- | The score of a hand uses the sum of its ranks as a tiebreaker.
type Score = (GroupType, Int)

-- | The score of a hand with the given type and ranks.
handScore :: GroupType -> Rank -> Rank -> Rank -> Score
handScore g r1 r2 r3 = (g, r1 + r2 + r3)

-- | The score of a hand with the given type and ranks, wrapped in a Just.
justHandScore :: GroupType -> Rank -> Rank -> Rank -> Maybe Score
justHandScore g r1 r2 r3 = Just (g, r1 + r2 + r3)

-- * Player
data Player = PlayerOne | PlayerTwo
              deriving (Eq, Enum, Show)

players = enumFrom PlayerOne

-- Given one player, what's the other?
otherPlayer :: Player -> Player
otherPlayer PlayerOne = PlayerTwo
otherPlayer PlayerTwo = PlayerOne

-- * Column
data Column =
    Column {
      groups  :: (CardGroup, CardGroup), -- the two facing groups
      claimer :: Maybe Player            -- who's won it?
    }
    deriving (Show)

emptyColumn =
    Column { groups = (emptyGroup, emptyGroup),
             claimer = Nothing }

-- | Which group in a column belongs to this player?
colGroup :: Column -> Player -> CardGroup
colGroup col PlayerOne = fst (groups col)
colGroup col PlayerTwo = snd (groups col)

-- | Set the group of a column belonging to a particular player.
setColGroup :: Column -> Player -> CardGroup -> Column
setColGroup col PlayerOne newGrp = col { groups=(newGrp, snd (groups col)) }
setColGroup col PlayerTwo newGrp = col { groups=(fst (groups col), newGrp) }

-- * Game State
data State =
    State {
      deck           :: [Card],           -- what's still in the deck?
      avail          :: [Card],           -- not on the board?
      timestamp      :: Int,              -- for timestamping Groups
      columns        :: Array Int Column, -- columns on the board
      hands          :: ([Card], [Card]), -- cards held by the two players
      currentPlayer :: Player             -- who's to move
    }
    deriving (Show)

instance Arbitrary State where
    arbitrary = do
      x <- arbitrary
      let g = randomGame (mkStdGen x) in do
        c <- choose (0, length (deck g) - 5)
        return g { deck = drop c $ deck g, avail = reverse $ L.sort $ drop c $ deck g}

colNumber :: Int -> State -> Column
colNumber colNo st = (columns st) ! colNo

getHand :: Player -> State -> [Card]
getHand PlayerOne = fst . hands
getHand PlayerTwo = snd . hands

setHand :: Player -> [Card] -> State -> State
setHand PlayerOne newHand st = st { hands=(newHand, snd (hands st)) }
setHand PlayerTwo newHand st = st { hands=(fst (hands st), newHand) }

flipPlayer :: State -> State
flipPlayer st = st { currentPlayer = otherPlayer (currentPlayer st) }

-- * Availability of cards
-- | Is this card potentially available?
cardAvail :: [Card] -> Rank -> Suit -> Bool
cardAvail av rank suit = elem (Card {rank=rank, suit=suit}) av

-- | rankAvail state suit r = true iff (suit,r) is in the deck.
rankAvail :: State -> Suit -> Rank -> Bool
suitAvail :: State -> Rank -> Suit -> Bool

rankAvail st suit rank = cardAvail (avail st) rank suit
suitAvail st rank suit = cardAvail (avail st) rank suit

-- | Are there any cards available with this rank?
anyOfRankAvail :: State -> Rank -> Bool
anyOfRankAvail st rank = any (suitAvail st rank) suits

-- | Return the best n cards available.
topNRanksAvail :: Int -> State -> [Card]
topNRanksAvail n = take n . avail

-- * Deck manipulation

newDeck :: [Card]
newDeck = [ Card { rank = r, suit = s } | r <- ranks, s <- suits ]

newGame :: State
newGame =
    State
    {
      deck           = newDeck,
      avail          = reverse $ L.sort newDeck,
      timestamp      = 0,
      columns        = listArray (1,9) (repeat emptyColumn),
      hands          = ([], []),
      currentPlayer  = PlayerOne
    }

randomGame :: (RandomGen r) => r -> State
randomGame g = newGame { deck = shuffle g newDeck }

gameWithDeck :: [Card] -> State
gameWithDeck cs = newGame { deck = cs, avail = reverse $ L.sort cs }

-- | Deal the top card from the deck; return it and the new state.
deckDeal :: State -> (Card, State)
deckDeal st = (c, st { deck = tail (deck st), avail = L.delete c (avail st) })
                where c = head (deck st)

-- | Deal a specific card from the deck; return it and the new state (for testing).
deckRemoveCard :: State -> Card -> (Card, State)
deckRemoveCard st c = (c, st { deck  = L.delete c (deck st),
                               avail = L.delete c (avail st) })

-- * Scoring

isStraight:: Rank -> Rank -> Rank -> Bool
isStraight x y z = a+1 == b && b+1 == c where [a,b,c] = L.sort [x,y,z]

computeScore :: [Card] -> Score
computeScore [x,y,z] =
    let flush        = suit x == suit y && suit y == suit z
        threeOfAKind = rank x == rank y && rank y == rank z
        sum          = rank x + rank y + rank z
        straight     = isStraight (rank x) (rank y) (rank z)
        category     = case (straight, flush, threeOfAKind) of
                         (True, True, _   ) -> StraightFlush
                         (_,    _,    True) -> ThreeOfAKind
                         (_,    True, _   ) -> Flush
                         (True, _,    _   ) -> Straight
                         _                  -> Random in
    (category, sum)
                                          
-- | Given cards x and y on the board, what's the best score the group
-- of cards could end up being worth?
bestPossibleScore2 :: Card -> Card -> State -> Score
bestPossibleScore2 x y st =
    let xr = rank x; xs = suit x; yr = rank y; ys = suit y
        flushPossible = (xs == ys)
        straightRanks =      -- list of ranks that could complete a straight
          L.filter (>=1) . L.filter (<=10) $
                     (case xr - yr of
                        -2 -> [xr+1]
                        -1 -> [yr+1,xr-1]
                        1  -> [xr+1,yr-1]
                        2  -> [xr-1]
                        _  -> [])
        checkStraightFlush =
            guard (flushPossible && not (null straightRanks)) >>
                      (L.find (rankAvail st xs) straightRanks) >>=
                      justHandScore StraightFlush xr yr
        checkThreeOfAKind =
            guard (xr == yr && anyOfRankAvail st xr) >>
                  justHandScore ThreeOfAKind xr xr xr
        checkFlush =
            guard flushPossible >>
                      (L.find (rankAvail st xs) ranks) >>=
                      justHandScore Flush xr yr
        checkStraight =
            (L.find (anyOfRankAvail st) straightRanks) >>=
            justHandScore Straight xr yr
        checkRandom =
            (L.find (anyOfRankAvail st) ranks) >>=
            justHandScore Random xr yr
    in firstJust [ checkStraightFlush,
                   checkThreeOfAKind,
                   checkFlush,
                   checkStraight,
                   checkRandom ]

bestPossibleScore1 :: Card -> State -> Score
bestPossibleScore1 x st =
    let av = avail st
        xr = rank x
        xs = suit x
        straightRanks =
            L.filter (\(r1, r2) -> 1 <= r1 && r1 <= 10 && 1 <= r2 && r2 <= 10)
             [ (xr+2, xr+1), (xr+1, xr-1), (xr-1, xr-2) ]
        checkStraightFlush =
            (\(r1, r2) -> handScore StraightFlush xr r1 r2) <$>
            L.find (\(r1, r2) -> cardAvail av r1 xs && cardAvail av r2 xs) straightRanks
        checkThreeOfAKind =
            guard (lengthAtLeast 2 $ L.filter (suitAvail st xr) suits) >>
            justHandScore ThreeOfAKind xr xr xr
        checkFlush =
            case take 2 (filter (rankAvail st xs) ranks) of
              [r1, r2] -> justHandScore Flush xr r1 r2
              _        -> Nothing
        checkStraight =
            L.find (\(r1, r2) -> anyOfRankAvail st r1 && anyOfRankAvail st r2) straightRanks >>=
             (\(r1, r2) -> justHandScore Straight xr r1 r2)
        checkRandom = Just (Random, xr + (sum $ map rank $ topNRanksAvail 2 st))
    in firstJust [ checkStraightFlush,
                   checkThreeOfAKind,
                   checkFlush,
                   checkStraight,
                   checkRandom ]

bestPossibleScore0 :: State -> Score
bestPossibleScore0 st =
    let checkStraightFlushOfRank r =
            any (\s -> all (rankAvail st s) [r, r-1, r-2]) suits
        checkThreeOfAKindOfRank r =
            length (take 3 $ filter (suitAvail st r) suits) == 3
        flushScore s =
            let bestRanks = take 3 $ L.filter (rankAvail st s) ranks
            in if (length bestRanks == 3)
               then Just (Flush, sum bestRanks)
               else Nothing
        checkStraightFlush =
            L.find checkStraightFlushOfRank [10,9..3] >>=
             (\r -> justHandScore StraightFlush r (r-1) (r-2))
        checkThreeOfAKind =
            L.find checkThreeOfAKindOfRank ranks >>=
             (\r -> justHandScore ThreeOfAKind r r r)
        checkStraight = 
            let checkStraight' r = all (anyOfRankAvail st) [r, r-1, r-2]
            in L.find checkStraight' [10,9..3] >>=
                (\r -> justHandScore Straight r (r-1) (r-2))
        checkFlush =
            foldr1 max $ map flushScore suits
        -- TODO: Straight
        checkRandom = Just (Random, (sum $ map rank $ take 3 $ avail st))
    in firstJust [ checkStraightFlush,
                   checkThreeOfAKind,
                   checkFlush,
                   checkStraight,
                   checkRandom ]

-- | What's the best possible eventual score for the given group?
bestPossibleScore :: [Card] -> State -> Score
bestPossibleScore cs@[x,y,z] st = computeScore cs
bestPossibleScore    [x,y]   st = bestPossibleScore2 x y st
bestPossibleScore    [x]     st = bestPossibleScore1 x st
bestPossibleScore    []      st = bestPossibleScore0 st

-- ** Testing

-- | Implements bestPossibleScore2 by actually creating all hands.
bestPossibleScore2Explicit :: Card -> Card -> State -> Score
bestPossibleScore2Explicit x y st =
    maximum [computeScore [x,y,z] | z <- deck st]

bestPossibleScore1Explicit :: Card -> State -> Score
bestPossibleScore1Explicit x st =
    maximum [bestPossibleScore2 x c st' | y <- deck st, let (c,st') = deckRemoveCard st y]

bestPossibleScore0Explicit :: State -> Score
bestPossibleScore0Explicit st =
    maximum [bestPossibleScore1 c st' | x <- deck st, let (c,st') = deckRemoveCard st x]

propScore0 st = bestPossibleScore0Explicit st == bestPossibleScore0 st
propScore1 st = let (c, st') = deckDeal st in
                bestPossibleScore1Explicit c st' == bestPossibleScore1 c st'
propScore2 st = let (c1, st')  = deckDeal st
                    (c2, st'') = deckDeal st' in
                bestPossibleScore2Explicit c1 c2 st'' == bestPossibleScore2 c1 c2 st''

-- * Groups

-- | Is g1 a finished group that can definitely beat g2?
beats :: CardGroup -> CardGroup -> State -> Bool
beats g1 g2 st = (computeScore (group g1), - groupTimestamp g1) > 
                 (bestPossibleScore (group g2) st, - groupTimestamp g2)
-- lower timestamp is better

-- | Add c to g, return new group and new state.
groupAddCard :: CardGroup -> Card -> State -> (CardGroup, State)
groupAddCard g c st = (CardGroup { group = c : group g, groupTimestamp = timestamp st },
                       st { timestamp = timestamp st + 1 })          

-- | Display a card group.
groupStr :: CardGroup -> Player -> String
groupStr g p = unwords $ map ((printf "%3s") . show) cards
    where cards = case p of
                    PlayerOne -> group g
                    PlayerTwo -> reverse $ group g

-- * Columns

-- | Can player p claim column col?
canClaimCol :: Player -> Column -> State -> Bool
canClaimCol p col st = beats (colGroup col p) (colGroup col (otherPlayer p)) st

-- | Player p tries to claim column # colIdx; return new state if succeeded
claimCol :: Player -> Int -> State -> Maybe State
claimCol p colIdx st =
    let col = colNumber colIdx st in
    if canClaimCol p col st
    then Just st { columns = columns st // [(colIdx, (columns st ! colIdx) { claimer = Just p })] }
    else Nothing

-- | Display a column.
colStr :: Int -> State -> [Char]
colStr colIdx st =
    let col = colNumber colIdx st
        groupStrs = map (\p -> groupStr (colGroup col p) p) players
        claimStr = case claimer col of
                     Just PlayerOne -> " *     "
                     Just PlayerTwo -> "     * "
                     Nothing        -> "  [" ++ show colIdx ++ "]  " in
    (groupStrs !! 0) ++ claimStr ++ (groupStrs !! 1)


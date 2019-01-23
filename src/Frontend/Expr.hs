{-# language DeriveAnyClass #-}
module Frontend.Expr where

-- import Text.Megaparsec (SourcePos(..),unPos)

import Text.Parsix.Position

-- TODO: rewrite this to be efficient
-- data Span = Span Position Posision
  -- deriving (Show)

instance Pretty Span where
  prettyPrec p (Span a b) = -- pretty (sourceName a) <> " " <>
    f a <> "-" <> f b where
    f p = g (visualRow p + 1) <> ":" <> g (visualColumn p + 1)
    g x = pretty x

-- TODO: rename...
union :: Span -> Span -> Span
union (Span a _) (Span _ b) = Span a b

data Spanned a = a :~ Span
  deriving (Generic, Pretty, Functor)

type Expr' = Spanned Expr


  
instance Show Expr' where showsPrec i (e :~ _) = showsPrec i e 

-- TODO: figure out good syntax for typeclasses
-- mb we could just reuse implicit pi for type classes?
-- i.e. if F is a typeclass then {a : F} -> gets typeclass solving?
-- tempting!
-- or equivalently, implicit pi and maybe explicit pi too could be kind polymorphic
data Plicitness = Implicit | Explicit
  deriving (Show, Generic, Pretty)


data Expr =
    MacroE MacroCall
  | Var Text
  | App [Expr']
  | Ann Expr' Expr'
  | Parens Expr'
  | Lam [(Span,Text,Maybe Expr')] Expr'
  | Pi [(Span,Plicitness,Text,Expr')] Expr'
  | Arr Expr' Expr'
  | ConstraintArr Expr' Expr'
  | Underscore
  -- TODO: ann, implicit app, implicit lam
  deriving (Show, Generic, Pretty)


data MacroCall = MacroCall Expr' (Maybe (Span, Text))
  deriving (Show, Generic, Pretty)

-- TODO: implicit

data Definition = 
  -- f_{i j k} x : ty = a
  -- TODO: args, implicit args, more?
  -- probably just take a telecope
  Definition Text 
    -- levels
    (Maybe [Text])
    -- ty
    (Maybe Expr')
    -- val
    Expr'
  | MacroD MacroCall
  -- f : ty
  -- | TypeAnn Text Expr'
  -- TODO: f args : ty
  deriving (Show, Generic)

instance Pretty Definition

defnName :: Definition -> Text
defnName (Definition n _ _ _) = n

{-# LANGUAGE ExplicitForAll         #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE UndecidableInstances   #-}
{-# LANGUAGE AllowAmbiguousTypes    #-}
{-# LANGUAGE TypeInType             #-}
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module A( MonadState,  modify_,evalState,  evalStateT) where

import Prelude  hiding ((.))

import Control.Applicative
import Control.Monad.Identity
import Control.Monad.Trans
import Data.Kind (Type, Constraint)
import qualified Control.Monad.State.Strict as S

-- Add a bang to x and the performance increases by 60x
(.) :: (b -> c) -> (a -> b) -> a -> c
(.) f g = \(!x) -> f (g x) ; {-# INLINE (.) #-}


type family If (cond :: Bool) (a :: k) (b :: k) :: k where
  If cond   a a = a
  If 'True  a b = a
  If 'False a b = b

type family (a :: k) == (b :: l) where
    a == a = 'True
    a == b = 'False

type    State  s     = StateT s Identity
newtype StateT s m a = StateT (S.StateT s m a) deriving (Applicative, Alternative, Functor, Monad, MonadTrans)

uwS :: StateT s m a -> S.StateT s m a
uwS (StateT x) = x
wS :: S.StateT s m a -> StateT s m a
wS = StateT

type family StatesT ss m where
    StatesT '[]       m = m
    StatesT (s ': ss) m = StateT s (StatesT ss m)


type        DiscoverStateData    (l :: k) m = DiscoverStateData' k l m
type family DiscoverStateData' k (l :: k) m where
    DiscoverStateData' Type l m = l
    DiscoverStateData' k    l m = StateData l m

type TransStateData l t m = (DiscoverStateData l (t m) ~ DiscoverStateData l m)

type family StateData l m where
    StateData l (StateT s m) = If (MatchedBases l s) s (StateData l m)
    StateData l (t m)        = StateData l m

type family MatchedBases (a :: ka) (b :: kb) :: Bool where
    MatchedBases (a :: k) (b   :: k) = a == b
    MatchedBases (a :: k) (b t :: l) = MatchedBases a b
    MatchedBases (a :: k) (b   :: l) = 'False




-- === MonadState === --

-- Definitions

type             MonadState  l m = (MonadGetter l m, MonadSetter l m)
class Monad m => MonadGetter l m where get :: m (DiscoverStateData l m)
class Monad m => MonadSetter l m where put :: DiscoverStateData l m -> m ()

-- Instancess

instance                       Monad m                                                           => MonadGetter (l :: Type) (StateT l m) where get   = wS  S.get    ; {-# INLINE get #-}
instance                       Monad m                                                           => MonadSetter (l :: Type) (StateT l m) where put = wS . S.put  ; {-# INLINE put #-}
instance {-# OVERLAPPABLE #-}  MonadGetter l m                                                   => MonadGetter (l :: Type) (StateT s m) where get   = lift $ get @l   ; {-# INLINE get #-}
instance {-# OVERLAPPABLE #-}  MonadSetter l m                                                   => MonadSetter (l :: Type) (StateT s m) where put = lift . put @l  ; {-# INLINE put #-}
instance {-# OVERLAPPABLE #-} (Monad m, MonadGetter__ ok l (StateT s m), ok ~ MatchedBases l s)  => MonadGetter (l :: k)    (StateT s m) where get   = get__  @ok @l   ; {-# INLINE get #-}
instance {-# OVERLAPPABLE #-} (Monad m, MonadSetter__ ok l (StateT s m), ok ~ MatchedBases l s)  => MonadSetter (l :: k)    (StateT s m) where put = put__  @ok @l ; {-# INLINE put #-}
instance {-# OVERLAPPABLE #-} (Monad (t m), MonadTrans t, MonadGetter l m, TransStateData l t m) => MonadGetter (l :: k)    (t m)        where get   = lift $ get @l   ; {-# INLINE get #-}
instance {-# OVERLAPPABLE #-} (Monad (t m), MonadTrans t, MonadSetter l m, TransStateData l t m) => MonadSetter (l :: k)    (t m)        where put = lift . put @l ; {-# INLINE put #-}

-- Helpers

class Monad m => MonadGetter__ (ok :: Bool) l m where get__ :: m (DiscoverStateData l m)
class Monad m => MonadSetter__ (ok :: Bool) l m where put__ :: DiscoverStateData l m -> m ()

instance (Monad m, DiscoverStateData l (StateT s m) ~ s)  => MonadGetter__ 'True  l (StateT s m) where get__   = get @s          ; {-# INLINE get__ #-}
instance (Monad m, DiscoverStateData l (StateT s m) ~ s)  => MonadSetter__ 'True  l (StateT s m) where put__ = put @s         ; {-# INLINE put__ #-}
instance (MonadGetter l m, TransStateData l (StateT s) m) => MonadGetter__ 'False l (StateT s m) where get__   = lift $ get @l   ; {-# INLINE get__ #-}
instance (MonadSetter l m, TransStateData l (StateT s) m) => MonadSetter__ 'False l (StateT s m) where put__ = lift . put @l  ; {-# INLINE put__ #-}

-- Replicators

type family Monads__ p ss m :: Constraint where
    Monads__ p (s ': ss) m = (p s m, Monads__ p ss m)
    Monads__ p '[]       m = ()


-- === Top state accessing === --

type family TopStateData m where
    TopStateData (StateT s m) = s
    TopStateData (t m)        = TopStateData m



-- === Construction & running === --


runStateT  :: forall s m a.              StateT s m a -> s -> m (a, s)
evalStateT :: forall s m a. Functor m => StateT s m a -> s -> m a
runStateT    = S.runStateT  . uwS ; {-# INLINE runStateT  #-}
evalStateT m = fmap fst . runStateT m ; {-# INLINE evalStateT #-}

evalState :: forall s a. State s a -> s -> a
evalState = S.evalState . uwS ; {-# INLINE evalState #-}


-- === Generic state modification === --

modifyM  :: forall l s m a. (MonadState l m, s ~ DiscoverStateData l m) => (s -> m (a, s)) -> m a
modifyM_ :: forall l s m . (MonadState l m, s ~ DiscoverStateData l m) => (s -> m     s)  -> m ()
modify_  :: forall l s m . (MonadState l m, s ~ DiscoverStateData l m) => (s ->       s)  -> m ()
modify_   = modifyM_ @l . fmap return       ; {-# INLINE modify_  #-}
modifyM_  = modifyM  @l . (fmap.fmap) ((),) ; {-# INLINE modifyM_ #-}
modifyM f = do (a,t) <- f =<< get @l
               a <$ put @l t
{-# INLINE modifyM #-}


{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleContexts #-}


{-# LANGUAGE Strict #-}
module Main where

import Prelude as P
import A

incState :: MonadState Int m => m ()
incState = modify_ @Int succ
{-# INLINE incState #-}

repeatM :: Monad m => Int -> m a -> m ()
repeatM i f = let r 0 = pure (); r i' = f >> r (i' - 1) in r i
{-# INLINE repeatM #-}

main :: IO ()
main = print $ (flip (evalState @Int) 0 . flip (evalStateT @String) "" . flip (evalStateT @Char) 'x' . flip (evalStateT @()) ()) (repeatM 10000000 incState)

#!/usr/bin/env runghc

module Main where

import Distribution.Simple
import Distribution.Simple.Program
import System.Cmd
import System.Exit
import System.Posix.Files (fileExist)

main :: IO ()
main = defaultMainWithHooks simpleUserHooks {
         testHook = runTestScript
       }

runTestScript _args _flag _pd _lbi =
    do e1 <- fileExist "dist"
       e2 <- fileExist "dist-ghc6"
       let d = case (e1, e2) of
                 (True, True) -> error "Both dist and dist-ghc6 exist!"
                 (False, False) -> error "Neither dist nor dist-ghc6 exist!"
                 (True, False) -> "dist"
                 (False, True) -> "dist-ghc6"
       system (d ++ "/build/tests/tests") >>=
                  \ code -> if code == ExitSuccess then return () else error "Test Failure"

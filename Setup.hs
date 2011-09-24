#!/usr/bin/env runghc

module Main where

import Distribution.Simple
import Distribution.Simple.LocalBuildInfo (LocalBuildInfo(buildDir))
import Distribution.Simple.Program
import System.Cmd
import System.Exit
import System.Posix.Files (fileExist)

main :: IO ()
main = defaultMainWithHooks simpleUserHooks {
         testHook = runTestScript
       }

runTestScript _desc lbi _hooks _flags =
    system (buildDir lbi ++ "/build/tests/tests") >>= \ code ->
    if code == ExitSuccess then return () else error "Test Failure"

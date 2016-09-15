#!/usr/bin/env runghc

module Main where

import Distribution.Simple
import System.Directory (copyFile)

main :: IO ()
main = defaultMainWithHooks simpleUserHooks

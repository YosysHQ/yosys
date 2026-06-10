#!/usr/bin/env python3

import sys
sys.path.append("..")

import gen_tests_makefile

def main():
    gen_tests_makefile.generate(["-y", "-t"])

if __name__ == "__main__":
    main()



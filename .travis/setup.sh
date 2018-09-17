#! /bin/bash

set -e

source .travis/common.sh

##########################################################################

# Fixing Travis's git clone
echo
echo 'Fixing git setup...' && echo -en 'travis_fold:start:before_install.git\\r'
echo
git fetch --unshallow && git fetch --tags

# For pull requests, we get more info about the git source.
if [ z"$TRAVIS_PULL_REQUEST_SLUG" != z ]; then
	echo "- Fetching from pull request source"
	git remote add source https://github.com/$TRAVIS_PULL_REQUEST_SLUG.git
	git fetch source && git fetch --tags

	echo "- Fetching the actual pull request"
	git fetch origin pull/$TRAVIS_PULL_REQUEST/head:pull-$TRAVIS_PULL_REQUEST-head
	git fetch origin pull/$TRAVIS_PULL_REQUEST/merge:pull-$TRAVIS_PULL_REQUEST-merge

	git log -n 5 --graph pull-$TRAVIS_PULL_REQUEST-merge
fi

# For building branches we need to fix the "detached head" state.
if [ z"$TRAVIS_BRANCH" != z ]; then
	TRAVIS_COMMIT_ACTUAL=$(git log --pretty=format:'%H' -n 1)
	echo "- Fixing detached head (current $TRAVIS_COMMIT_ACTUAL -> $TRAVIS_COMMIT)"
	git remote -v
	git branch -v
	if [ x"$(git show-ref -s HEAD)" = x"$TRAVIS_COMMIT" ]; then
		echo "Checked out at $TRAVIS_COMMIT"
	else
		if [ z"$TRAVIS_PULL_REQUEST_SLUG" != z ]; then
			git fetch source $TRAVIS_COMMIT || echo "Unable to fetch $TRAVIS_COMMIT from source"
		fi
		git fetch origin $TRAVIS_COMMIT || echo "Unable to fetch $TRAVIS_COMMIT from origin"
	fi
	git branch -D $TRAVIS_BRANCH || true
	git checkout $TRAVIS_COMMIT -b $TRAVIS_BRANCH
	git branch -v
fi

# Output status information.
git status
git describe --tags
git log -n 5 --graph
echo
echo -en 'travis_fold:end:before_install.git\\r'
echo

##########################################################################

# Mac OS X specific setup.
if [[ "$TRAVIS_OS_NAME" == "osx" ]]; then
	(
		echo
		echo 'Setting up brew...' && echo -en 'travis_fold:start:before_install.brew\\r'
		echo
		brew update
		brew tap Homebrew/bundle
		brew bundle
		brew install ccache
		brew install gcc@7
		echo
		echo -en 'travis_fold:end:before_install.brew\\r'
		echo
	)
fi

##########################################################################

# Install iverilog
(
	if [ ! -e ~/.local-bin/bin/iverilog ]; then
		echo
		echo 'Building iverilog...' && echo -en 'travis_fold:start:before_install.iverilog\\r'
		echo
		mkdir -p ~/.local-src
		mkdir -p ~/.local-bin
		cd ~/.local-src
		git clone git://github.com/steveicarus/iverilog.git
		cd iverilog
		autoconf
		./configure --prefix=$HOME/.local-bin
		make
		make install
		echo
		echo -en 'travis_fold:end:before_install.iverilog\\r'
		echo
	fi
)

##########################################################################

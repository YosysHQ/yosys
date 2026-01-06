# Introduction

Thanks for thinking about contributing to the Yosys project.  If this is your
first time contributing to an open source project, please take a look at the
following guide:
https://opensource.guide/how-to-contribute/#orienting-yourself-to-a-new-project.

Information about the Yosys coding style is available on our Read the Docs:
https://yosys.readthedocs.io/en/latest/yosys_internals/extending_yosys/contributing.html.

# Using the issue tracker

The [issue tracker](https://github.com/YosysHQ/yosys/issues) is used for
tracking bugs or other problems with Yosys or its documentation.  It is also the
place to go for requesting new features.
When [creating a new issue](https://github.com/YosysHQ/yosys/issues/new/choose),
we have a few templates available.  Please make use of these!  It will make it
much easier for someone to respond and help.

### Bug reports

Before you submit an issue, please check out the [how-to guide for
`bugpoint`](https://yosys.readthedocs.io/en/latest/using_yosys/bugpoint.html).
This guide will take you through the process of using the [`bugpoint`
command](https://yosys.readthedocs.io/en/latest/cmd/bugpoint.html) in Yosys to
produce a [minimal, complete and verifiable
example](https://stackoverflow.com/help/minimal-reproducible-example) (MVCE).
Providing an MVCE with your bug report drastically increases the likelihood that
someone will be able to help resolve your issue.


# Using pull requests

If you are working on something to add to Yosys, or fix something that isn't
working quite right, make a [PR](https://github.com/YosysHQ/yosys/pulls)!  An
open PR, even as a draft, tells everyone that you're working on it and they
don't have to.  It can also be a useful way to solicit feedback on in-progress
changes.  See below to find the best way to [ask us
questions](#asking-questions).

In general, all changes to the code are done as a PR, with [Continuous
Integration (CI)](https://github.com/YosysHQ/yosys/actions) tools that
automatically run the full suite of tests compiling and running Yosys.  Please
make use of this!  If you're adding a feature: add a test!  Not only does it
verify that your feature is working as expected, but it can also be a handy way
for people to see how the feature is used.  If you're fixing a bug: add a test!
If you can, do this first; it's okay if the test starts off failing - you
already know there is a bug.  CI also helps to make sure that your changes still
work under a range of compilers, settings, and targets.


### Labels

We use [labels](https://github.com/YosysHQ/yosys/labels) to help categorise
issues and PRs.  If a label seems relevant to your work, please do add it; this
also includes the labels beggining with 'status-'.  The 'merge-' labels are used
by maintainers for tracking and communicating which PRs are ready and pending
merge; please do not use these labels if you are not a maintainer.


# Asking questions

If you have a question about how to use Yosys, please ask on our [Discourse forum](https://yosyshq.discourse.group/) or in our [discussions
page](https://github.com/YosysHQ/yosys/discussions).
The Discourse is also a great place to ask questions about developing or
contributing to Yosys.

We have open [dev 'jour fixe' (JF) meetings](https://docs.google.com/document/d/1SapA6QAsJcsgwsdKJDgnGR2mr97pJjV4eeXg_TVJhRU/edit?usp=sharing) where developers from YosysHQ and the
community come together to discuss open issues and PRs.  This is also a good
place to talk to us about how to implement larger PRs.

#lang scribble/base
@(require scribble/manual
          (for-label racket))

@title{Racket Packages}
@author{Jay McCarthy}

The state of packaging in Racket is not where it must be.

@section{Problems with current regime}

Before presenting the new proposal, I review what I see the problems are with what we have now.
I think of these as "test cases" on the new package system. If these are not adequate, then
the new package system is unlikely to be worth it.

@local-table-of-contents[]

@subsection{PLaneT packages are second-class}

First, they cannot come with a distribution.
Second, they are required in a very different way: @racket[(require xml)] vs
@racket[(require (planet jay-mccarthy:1:1/xml))]. Third, their documentation is not searchable
unless it is indexed.

@subsection{PLaneT packages are hard to upgrade}

The semantics of PLaneT linking is confusing to many users and emphasizes stability as the default
rather than the exception. This is partly because of the internal linking and partly because of the
caching of old links, even after packages are uninstalled.

@subsection{PLaneT code is not easy to improve}

It is very difficult to find the code that implements a PLaneT package on your system so you can improve
or test it because of the deep and exotic directory structure. The PLaneT server does not provide a good
way of communicating with the author of a package.

@subsection{PLaneT packages are hard to discover or trust}

When someone installs a fresh Racket installation, there is no indication that PLaneT even exists from the installer
or from inside of DrRacket, etc. Even if someone discovers the site, it is very difficult to figure out what packages
are worth investigating to see what they do and/or gaining trust in them.

@subsection{PLaneT is too centralized}

It is not easy to run PLaneT mirrors, private PLaneT servers, or collaborate/distribute with others using Racket
without going through the centralized PLaneT server.

@subsection{The core is too big}

The core distribution is very large from the perspective of pure size and from the perspective of understandability
and scope. 

...

@subsection{Pieces of the core cannot be held-back}

...

@subsection{There is no migration from the core to PLaneT or vice versa}

...

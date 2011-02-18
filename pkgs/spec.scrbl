#lang scribble/base
@(require scribble/manual
          (for-label racket))

@title{Racket Packages}
@author{Jay McCarthy}

The state of packaging in Racket is not where it must be.

@local-table-of-contents[#:style 'immediate-only]

@section{Problems with current regime}

Before presenting the new proposal, I review what I see the problems are with what we have now.
I think of these as "test cases" on the new package system. If these are not adequate, then
the new package system is unlikely to be worth it.

@subsection{PLaneT packages are second-class}

First, they cannot come with a distribution: it is not possible for Racket developers to provide installers for a Racket instance that includes PLaneT packages. This affects core developers and educators in particular: This affects core developers by encouraging more and more functionality in the core. (For example, Redex was once separate, but was moved in for convenience.) This affects educators because it complicates their installation instructions and puts pressure to move textbook support into the core (c.f. PLAI, Picturing Programs, HTDP, DMDA, etc.) 

Second, they are required in a very different way: @racket[(require xml)] vs
@racket[(require (planet jay-mccarthy:1:1/xml))]. A module that uses a PLaneT package is not insulated from the usage of PLaneT. This makes it hard to migrate things to and from PLaneT. It places distribution details throughout the code of a collection, rather than in a central location.

Third, their documentation is not searchable unless it is installable. Our online documentation system is not useful for exploring PLaneT libraries. Additionally, if PLaneT packages wish to cross-reference, that causes an installation, which discourages useful mentions of other packages.

@subsection{PLaneT packages are hard to upgrade}

Packages are hard to upgrade because of the linking rules and the internal linking.

The semantics of PLaneT linking is confusing to many users and emphasizes stability as the default
rather than the exception. (If a module requires a package without a version number, it gets the most recent major and minor at the time it is compiled. However, if the local cache contains any version, that version is assumed to be the right version without recourse to the server. If a major version is specified, then the same process happens, but restricted to that major version---which may causes a server pull, even if the cache contains a version of the package. If a minor version is specified, then a version newer than that must be used; this options only exists to refuse to use a cache version if it is too old. If a minor version is specified with =, then that version is used. Once a module is linked, according to the previous algorithm, it stays linked to that forever, until the local cache is cleaned and it is recompiled.) It is unfortunate that there is no interface in the command-line tool to clear the cache.

PLaneT uses internal linking (meaning that modules specify which PLaneT package at what version, as mentioned above) rather than external linking (where a module would specify that it needs "xml" and it would be part of a "project" that specifies that the "xml" module is provided by such and such a package.)

@subsection{PLaneT code is not easy to improve}

Although all PLaneT packages are de facto open source, it is very difficult to find the code that implements a PLaneT package on your system so you can improve or test it because of the deep and exotic directory structure. Supposing you did that, the PLaneT Web app does not provide a good way of communicating with the author of a package and tracking such things.

@subsection{PLaneT packages are hard to discover or trust}

When someone installs a fresh Racket installation, there is no indication that PLaneT even exists from the installer or from inside of DrRacket, etc. Even if someone discovers the site, it is very difficult to figure out what packages are worth investigating to see what they do and/or gaining trust in them. The amount of duplication on the Web page and the shallow hierarchy make it even more difficult to even discover what options are available.

@subsection{PLaneT is too centralized}

It is not easy to run PLaneT mirrors, private PLaneT servers, or collaborate/distribute with others using Racket without going through the centralized PLaneT server. This is especially problematic given the de facto open source of the centralized PLaneT server.

@subsection{The core is too big}

The core distribution is very large from the perspective of pure size and from the perspective of understandability and scope. The collects tree is over 200MB compiled. It contains half a dozen text book support library most people will not use. It is difficult to separate out the GUI correctly (as evidenced by the periodic dist-specs errors.) It contains barely supported collections (Algol 60, FrTime, MysterX, etc.) 

@subsection{Pieces of the core cannot be held-back}

Since the core is so big, many users would like to upgrade one piece, while leaving others constant. For example, a common request is to be able to keep an old version of the Web server, while upgrading the core Racket VM. There's no principled reason why this could not be done, because they are mostly separate and changes to the core rarely require immediate changes to the Web server, due to Matthew's great ability to maintain backwards compatibility. However, it is simply not an option to do this. The prospect of manually fusing collects trees is an unreasonable burden on programmers. Such a decomposition and independent upgrades would have been very useful, for example, in testing GR2. 

@subsection{There is no migration from the core to PLaneT or vice versa}

This issue is briefly mentioned above, but given the difficulty of upgrading and the second-class-ness of PLaneT, we do not observe much movement between the core and PLaneT. It is too difficult to pull things out of the core and start distributing them on PLaneT because of the disadvantages of PLaneT. Additionally, if we want to move things into the core, to give them more visibility (itself a symptom of another problem), the PLaneT version has been maintained anyways. (Just ask me for PLAI, Carl for scheme.plt, etc.)

@subsection{Installations are expensive}

When a PLaneT package is installed, the compilation process is very expensive, especially when documentation building and re-indexing is counted. The PLaneT server (or packager) could conceivably provide already compiled versions of all these things for use by the end user.

@subsection{Poor security defaults}

The security defaults for PLaneT are very poor. For example, there is no verification that the right file came through; there is no check that the real PLaneT server was reached; the program is compiled without a sandbox (and since macros are infinitely powerful, compilation can mean compromise); a module can spawn PLaneT installations in sub-modules far away; etc.

@subsection{Nothing is ever private}

In Racket we have a convention of naming subdirectories of packages @filepath{private} but this does not actually prevent anything outside the package from in fact using these modules.

@section{Good things about the current regime}

Nevertheless, there are still some good things about PLaneT that we should maintain.

@subsection{It just works}

Modules are totally self-contained in their dependencies and packages automatically install. Contrast this to Perl where may have to iterate to a fixed-point attempting to run a script to discover its dependencies and install them as you go. In effect, there is zero system administration of the packages installed on a system.

@subsection{Free hosting of source in central place}

It is good that we provide a free host to serve and learn about packages.

@subsection{Package preview is very easy}

It is good that the PLaneT site provides easy access to all versions of a package with their documentation and source readily apparent.

@section{Going forward}

With these issues in mind, we'd like to improve the situation. As a first step, I think it is important to distinguish between a packaging system and a package distribution and discovery system.

As it stands, we have a packaging system (@filepath{.plt} files) with many complicated features that aren't really used (as far as I know) and an integrated packaging and package distribution system (PLaneT) that sits atop @filepath{.plt}s, but reimplements some features.

The perspective I'd like to take in improving packages in Racket is to start from a strict separation of packages and package distribution, then expand the capabilities of our base packages, then build a more liberal and modern package distribution system.

@section{Packages}

In this section I talk about some of the properties of the packaging system at high-level then try to specify some low-level possible implementations.

@subsection{Vocabulary}

A @deftech{module} is the standard Racket module: a single file with dependencies and phased exports. For example, @filepath{web-server/web-server.rkt} is a module.

A @deftech{collection} is a tree of @tech{module}s and associated data. For example, @filepath{web-server} is a collection of many modules and a few data files.

A @deftech{package} is a set of @tech{collection}s and metadata. For example, the Web Server package might contain the @filepath{web-server} and @filepath{tests/web-server} collections; the DrRacket package might contain the @filepath{drracket} and @filepath{drscheme} collections (one provides backward compatibility, of course.)

Package metadata includes at least an identifier, a natural number version, @tech{package} dependencies, and @tech{module} protection information. For example, the Web Server package may be identified by @filepath{racket-web-server}, at version 30, depend on the XML package version 49 or higher, and mark @filepath{web-server/private} as private.

An @deftech{installation} is a set of @tech{package}s such that each pairing of an identifier and a particular version appears at most once. For example, the Web Server version 30 may not be in an installation twice. This does @emph{not} preclude packages installed at different versions (Web Server version 30 and 31) or packages with common modules (both the Xexpr and the SXML package providing a public @filepath{xml} module.)

@subsection{Principles}

Modules should not need to reference anything about the package they are apart of or that they depend on. This information will derived from their location on the filesystem, similar to our current collections.

Installing a new version of package (version 40 to 41) will affect all dependents of that package, by default.

Package dependencies may be "frozen" at their current versions to ensure that no future installation operation will affect them.

Backwards incompatible changes of a package will require a new package identifier. (Similar to libgtk and libgtk2.)

Module protection information is respected.

Packageless modules should have an easy to determine set of modules available to them from the set of installed packages preferring newer versions.

Locating an installed module should be easy and in most cases, obvious.

Uninstalling packages should be possible.

@subsection{Plausible Implementation}

(These details are much less important than what appears above. At the least they are an attempt to show that the above is feasible with minimal changes to the existing Racket infrastructure.)

An installation could be divided into @racket[_n] heaps where @racket[_n] is at least @racket[2] for a user and system heap. (Other heaps could serve a group (i.e. class) specific heaps.)

Each heap would contain information about installed packages---such as why they were installed (for something like @exec{apt-get autoremove}) and whether their dependencies are frozen---in a heap level database: @filepath{<heap>/install.rktd}.

Packages would be simple archives (as opposed to our homegrown @filepath{.plt}s) containing a metadata file (@filepath{info.rkt}) and collection directories.

The package heaps would be structured as @filepath{<heap>/<package-id>/<version>/<collect>} where the contents of the collections is identical to the package source.

Each package's installation (@filepath{<heap>/<package-id>/<version>}) would contain a linking directory (@filepath{.links}) with shadow modules for every module visible to them. For example,
@filepath{system/web-server/30/.links/xml/main.rkt} would roughly be:
@racketmod[racket/shadow
           (require (real system/xml/49/xml/main))
           (provide (all-from-out (real system/xml/49/xml/main)))]
Modules not written in the restricted shadow language would not see the "heap level" of modules and could not use the "real" modules, instead @racket[(require xml)] in the Web Server package would transparently be rewritten to @racket[(require (real system/web-server/30/.links/xml))] and rely on the package installation to locate the real module. This includes modules that are part of the package. (N.B. The use of shadow modules specifically does not rely on filesystem links that are confusing and do not work on Windows.)

A well-known package (@filepath{<heap>/SYSTEM/+inf.0/}) would contain a linking directory that serves as the default for packageless modules. This would contain the most recent version of all package modules and prefer the last installed package when two packages have conflicting modules. (This ensures that new unpackaged code by default uses the newer versions of everything.)

@subsection{Discussion}

This implementation requires very little change from the implementation depending on the level of module protection offered. For example, it appears to me that a standard @racket[require] transformer in the @racketmodname[racket] language could implement the shadow name mangling and we could use unprovided syntax to protect the underlying real @racket[require] form. After that, the various heaps would leverage the existing support for a collection search path. It would require the module level splicing, which is already implemented.

This implementation plays well with versioning systems because the sources of packages are kept distinct and on a development system (on operating system where it exists) filesystem links could directly tie repositories and installations.

This implementation provides good support for structuring the core collections as a few packages and ensures that dependencies can't form behind your back (as witness by the many distspec breaks) because all modules see modules from their linking directory rather than the current installation.

I can't really judge how well this implementation keeps things "in the language". It relies on the state established by the package installer to give meaning to programs and that state is controlled by the package's @filepath{info.rkt} file. However, this might be a realistic sweet-spot given the importance of packages to the program development and deployment environment.

I think the biggest problem with this implementation is that without a tool it could be confusing to figure out what module file a require statement in a program will resolve to. For example, you have to look in the linking directory (and know to look there), read the fully expanded name, then look at that file. In what I believe to be the common case where there is a single version of every package and no conflicting packages it is very obvious which module will be used, provided you know what package provides a collect. I also think it will be common for packages to provide one collect, with the same name, so hopefully that will be easy to. The situation is the same for packageless files although there is an interesting problem in that the meaning of a program can change because changes in the installation state. Even when that occurs, I think the rule of most new packages is easy to follow.

Here's a strawman implementation that I think solves that problem: There is a single heap and non-conflicting modules are copied into it, preferring the first installed version. When a new package conflicts with an older one, it is stored in a special name-mangled place. All modules can access everything in the heap, but we perform a simple analysis when compiling to error if other modules (private or non-dependents) are used. When you look at the heap, you cannot tell what module came from what package, but you can easily tell what modules are visible. I think this technique requires more core changes, interacts poorly with versioning systems (because of copying) [think, for example, what our @filepath{.gitignore} will contain in the core repository and how we will develop the core and do other work with some packages installed; either the rules will be complicated or we'll need a separation of the source and installation even for the core], depending on how the module protection works it may be easy to accidentally create dependencies, and finally it keeps the meaning of programs totally "in the language" because the state of packages is almost invisible to the runtime. Clearly this is my strawman and I don't think these "costs" are worth it, I'd like to know your opinion and proposed implementation.

@section{Glue between installation and distribution}

The packaging system only deals with what happens to packages when the get installed while the distribution deals with how they get there. These could be TOTALLY @emph{separate} where packages refer to identifiers with no definite connection to the distribution system OR they could totally @emph{connected} where packages refer to the distribution system explicitly (as in PLaneT.)

I think there should be a loose connection. This is to facilitate easy installation with downloading a bunch of tarballs and installing them one-by-one (like old Linux distributions) and facilitate easy upgrade by keeping a connection between installed packages and where they came from.

My explicit proposal: package identifiers are valid URL path elements ending in @filepath{.rkb} (Racket Ball, obviously); a package metadata file may contain a dependency specification like @filepath{web-server.rkb/=40} or @filepath{web-server.rkb/40} for exactly 40 and at least 40 respectively; a metadata file @emph{may} also specify a URL ending in such a specification, like @filepath{http://planet.racket-lang.org/pkgs/web-server.rkb/=40} or @filepath{https://secured00d.nsa.gov/sekrut/web-server.rkb/=41}, etc. If such a URL is given, it simply specifies a default place to find the package if it is not already available, but @emph{any} @filepath{web-server.rkb} package will do.

Every URL-less specification will implicitly reference the centrally hosted PLaneT server.

A standard file-based protocol will exist between package clients and package servers so no special software with intricate setups will be necessary to start a new package server. This will facilitate private servers and official mirrors.

Upgrades could be facilitated by checking the version returned by GET-ing @filepath{http://planet.racket-lang.org/pkgs/web-server.rkb} which would REDIRECT to @filepath{http://planet.racket-lang.org/pkgs/web-server.rkb/=@racket[_newest]}. Thus, the URL originally used to install the package (if it was not already located on the filesystem) would be saved to allow update checking, etc.
         
@section{Package Distribution}

The package distribution system (PLaneT) is easy to change and evolve as we go, provided we use a simple URL/HTTP-based mechanism for the clients. 

I do have a few ideas and basic things to suggest:
@itemize[
         @item{Give away accounts as we do now.}
         @item{Allow package submission from the command line by using a HTTP POST with an AUTH header.}
         @item{Provide a simple interface to remove and replace packages (including old versions) arbitrarily.}
         @item{Restrict package names to be prefixed by the user name of the account.}
         @item{Use social tags to filter and categorize packages. No fixed vocabulary.}
         @item{Use Amazon-style review system to establish reputation.}
         @item{Connect to existing @emph{external} bug tracking systems like Launchpad and Github via package metadata.}
         @item{Use reputation to "bless" packages with prefix-less names. For example, jay-mccarthy:mongodb.rkb might become mongodb.rkb after such a blessing.}
         @item{Use Google custom search to package documentation/source.}
         @item{Allow the use of checksums and HTTPS to ensure package contents are as expected.}
         @item{Use moderators to "black ball" malicious packages.}
]

These ideas give clear priority to leveraging existing tools and limiting the amount of pain and maintenance for PLaneT.

Some decisions in the packaging layer have big effects on the distribution system, in particular give it the ability to drop certain issues. For example, it is easy to improve a package because you can easily find and change the code on your system then if the maintainer isn't available, you can make a new package with the same module names (so the switch requires no changes in code), then leave a review for the old package directing users to the new one, etc.

@section{Final Thoughts}

There are a few big open problems in my mind:
@itemize[
         @item{Informing new users on installation what packages they might want. We could use the reputation and download counts, but we currently have no final "Get Packages" step in our installers.}
         @item{Interacting with operating system distribution. Hopefully this more file-based infrastructure would ease the process, but I don't really know much about this.}
         @item{Removing the pain of installation by keeping safe ZOs on the server.}
         @item{Once this infrastructure is in place, we should spend a good amount of time breaking the core into packages that are distributed optionally and separately. I believe this requires a good "post install" to keep the batteries included, so to speak.}
]

Lastly, clearly the existing PLaneT infrastructure needs to stay in place, but I think it should be a vestigial structure that withers away.

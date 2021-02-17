<!DOCTYPE html>
<html class="" lang="en">
<head prefix="og: http://ogp.me/ns#">
<meta charset="utf-8">
<link as="style" href="https://gitlab.math.univ-paris-diderot.fr/assets/application-bf1ba5d5d3395adc5bad6f17cc3cb21b3fb29d3e3471a5b260e0bc5ec7a57bc4.css" rel="preload">
<link as="style" href="https://gitlab.math.univ-paris-diderot.fr/assets/highlight/themes/white-0678dba52a34ddc3b009cf294c54cfbddb9bac5991d6377ab811afe156e5a0cb.css" rel="preload">
<link as="font" href="https://gitlab.math.univ-paris-diderot.fr/assets/fontawesome-webfont-2adefcbc041e7d18fcf2d417879dc5a09997aa64d675b7a3c4b6ce33da13f3fe.woff2?v=4.7.0" rel="preload" type="font/woff2">

<meta content="IE=edge" http-equiv="X-UA-Compatible">

<meta content="object" property="og:type">
<meta content="GitLab" property="og:site_name">
<meta content="2-preuves/other-provers/isabelle/IFOLBIS.thy · master · Pierre Letouzey / coq-lmfi" property="og:title">
<meta content="Cours de Coq au M2 LMFI (partie 1 programmation fonctionnelle + partie 2 preuves formelles)" property="og:description">
<meta content="https://gitlab.math.univ-paris-diderot.fr/assets/gitlab_logo-7ae504fe4f68fdebb3c2034e36621930cd36ea87924c11ff65dbcb8ed50dca58.png" property="og:image">
<meta content="64" property="og:image:width">
<meta content="64" property="og:image:height">
<meta content="https://gitlab.math.univ-paris-diderot.fr/letouzey/coq-lmfi/-/blob/master/2-preuves/other-provers/isabelle/IFOLBIS.thy" property="og:url">
<meta content="summary" property="twitter:card">
<meta content="2-preuves/other-provers/isabelle/IFOLBIS.thy · master · Pierre Letouzey / coq-lmfi" property="twitter:title">
<meta content="Cours de Coq au M2 LMFI (partie 1 programmation fonctionnelle + partie 2 preuves formelles)" property="twitter:description">
<meta content="https://gitlab.math.univ-paris-diderot.fr/assets/gitlab_logo-7ae504fe4f68fdebb3c2034e36621930cd36ea87924c11ff65dbcb8ed50dca58.png" property="twitter:image">

<title>2-preuves/other-provers/isabelle/IFOLBIS.thy · master · Pierre Letouzey / coq-lmfi · GitLab</title>
<meta content="Cours de Coq au M2 LMFI (partie 1 programmation fonctionnelle + partie 2 preuves formelles)" name="description">
<link rel="shortcut icon" type="image/png" href="/assets/favicon-7901bd695fb93edb07975966062049829afb56cf11511236e61bcf425070e36e.png" id="favicon" data-original-href="/assets/favicon-7901bd695fb93edb07975966062049829afb56cf11511236e61bcf425070e36e.png" />

<link rel="stylesheet" media="all" href="/assets/application-bf1ba5d5d3395adc5bad6f17cc3cb21b3fb29d3e3471a5b260e0bc5ec7a57bc4.css" />

<link rel="stylesheet" media="all" href="/assets/application_utilities-4a0a7fb4b050255fc637b897e541f513df1cdf23cb1518fabc4323f2d0b78866.css" />
<link rel="stylesheet" media="all" href="/assets/themes/theme_indigo-1e3c170ae7fd24d137960957cba8221abf63a78f8b108e77f131b0fed6a659c7.css" />

<link rel="stylesheet" media="all" href="/assets/highlight/themes/white-0678dba52a34ddc3b009cf294c54cfbddb9bac5991d6377ab811afe156e5a0cb.css" />


<script>
//<![CDATA[
window.gon={};gon.api_version="v4";gon.default_avatar_url="https://gitlab.math.univ-paris-diderot.fr/assets/no_avatar-849f9c04a3a0d0cea2424ae97b27447dc64a7dbfae83c036c45b403392f0e8ba.png";gon.max_file_size=10;gon.asset_host=null;gon.webpack_public_path="/assets/webpack/";gon.relative_url_root="";gon.shortcuts_path="/help/shortcuts";gon.user_color_scheme="white";gon.gitlab_url="https://gitlab.math.univ-paris-diderot.fr";gon.revision="eaa194f15e6";gon.gitlab_logo="/assets/gitlab_logo-7ae504fe4f68fdebb3c2034e36621930cd36ea87924c11ff65dbcb8ed50dca58.png";gon.sprite_icons="/assets/icons-1e863578ceb6844cc6941dadfd4b07001aed5876dc579fe61ea58ffd1458e7e8.svg";gon.sprite_file_icons="/assets/file_icons-c13caf2f3ca00cc2c02b11d373ac288c200b9b4dcddbb52a5027dc07b3eece19.svg";gon.emoji_sprites_css_path="/assets/emoji_sprites-289eccffb1183c188b630297431be837765d9ff4aed6130cf738586fb307c170.css";gon.test_env=false;gon.disable_animations=null;gon.suggested_label_colors={"#0033CC":"UA blue","#428BCA":"Moderate blue","#44AD8E":"Lime green","#A8D695":"Feijoa","#5CB85C":"Slightly desaturated green","#69D100":"Bright green","#004E00":"Very dark lime green","#34495E":"Very dark desaturated blue","#7F8C8D":"Dark grayish cyan","#A295D6":"Slightly desaturated blue","#5843AD":"Dark moderate blue","#8E44AD":"Dark moderate violet","#FFECDB":"Very pale orange","#AD4363":"Dark moderate pink","#D10069":"Strong pink","#CC0033":"Strong red","#FF0000":"Pure red","#D9534F":"Soft red","#D1D100":"Strong yellow","#F0AD4E":"Soft orange","#AD8D43":"Dark moderate orange"};gon.first_day_of_week=0;gon.ee=false;gon.features={"webperfExperiment":false,"snippetsBinaryBlob":false,"usageDataApi":true,"securityAutoFix":false,"startupCss":false,"gitlabCiYmlPreview":false};gon.experiments={"suggestPipeline":false};
//]]>
</script>



<script src="/assets/webpack/runtime.8fce4aa0.bundle.js" defer="defer"></script>
<script src="/assets/webpack/main.e89d0618.chunk.js" defer="defer"></script>
<script src="/assets/webpack/commons-globalSearch-pages.admin.abuse_reports-pages.admin.groups.show-pages.admin.projects-pages.ad-c08b40ef.a8bba176.chunk.js" defer="defer"></script>
<script src="/assets/webpack/commons-pages.groups.boards-pages.groups.details-pages.groups.show-pages.projects-pages.projects.act-5eeff683.eaa04149.chunk.js" defer="defer"></script>
<script src="/assets/webpack/commons-pages.admin.application_settings-pages.admin.application_settings.general-pages.admin.applic-5753b007.27b564d8.chunk.js" defer="defer"></script>
<script src="/assets/webpack/commons-pages.groups.milestones.edit-pages.groups.milestones.new-pages.projects.blame.show-pages.pro-77e8c306.37c1e60d.chunk.js" defer="defer"></script>
<script src="/assets/webpack/commons-pages.projects.blame.show-pages.projects.blob.edit-pages.projects.blob.new-pages.projects.bl-c6edf1dd.8ca8706d.chunk.js" defer="defer"></script>
<script src="/assets/webpack/commons-pages.projects.blob.show-pages.projects.shared.web_ide_link-pages.projects.show-pages.projec-cf300cc3.f4db049e.chunk.js" defer="defer"></script>
<script src="/assets/webpack/pages.projects.blob.show.d06c9cb3.chunk.js" defer="defer"></script>


<meta name="csrf-param" content="authenticity_token" />
<meta name="csrf-token" content="EfI1yiKfkhrQv/jNw6vnWBuikKa1P69t7ncTZuxwLrfaHu78rdAjgrSeDdgNXh22GiUA7on5pr0bgs7+hxd9xQ==" />
<meta name="csp-nonce" />
<meta name="action-cable-url" content="/-/cable" />
<meta content="width=device-width, initial-scale=1, maximum-scale=1" name="viewport">
<meta content="#474D57" name="theme-color">
<link rel="apple-touch-icon" type="image/x-icon" href="/assets/touch-icon-iphone-5a9cee0e8a51212e70b90c87c12f382c428870c0ff67d1eb034d884b78d2dae7.png" />
<link rel="apple-touch-icon" type="image/x-icon" href="/assets/touch-icon-ipad-a6eec6aeb9da138e507593b464fdac213047e49d3093fc30e90d9a995df83ba3.png" sizes="76x76" />
<link rel="apple-touch-icon" type="image/x-icon" href="/assets/touch-icon-iphone-retina-72e2aadf86513a56e050e7f0f2355deaa19cc17ed97bbe5147847f2748e5a3e3.png" sizes="120x120" />
<link rel="apple-touch-icon" type="image/x-icon" href="/assets/touch-icon-ipad-retina-8ebe416f5313483d9c1bc772b5bbe03ecad52a54eba443e5215a22caed2a16a2.png" sizes="152x152" />
<link color="rgb(226, 67, 41)" href="/assets/logo-d36b5212042cebc89b96df4bf6ac24e43db316143e89926c0db839ff694d2de4.svg" rel="mask-icon">
<meta content="/assets/msapplication-tile-1196ec67452f618d39cdd85e2e3a542f76574c071051ae7effbfde01710eb17d.png" name="msapplication-TileImage">
<meta content="#30353E" name="msapplication-TileColor">




</head>

<body class="ui-indigo tab-width-8  gl-browser-chrome gl-platform-mac" data-find-file="/letouzey/coq-lmfi/-/find_file/master" data-namespace-id="52" data-page="projects:blob:show" data-page-type-id="master/2-preuves/other-provers/isabelle/IFOLBIS.thy" data-project="coq-lmfi" data-project-id="681">

<script>
//<![CDATA[
gl = window.gl || {};
gl.client = {"isChrome":true,"isMac":true};


//]]>
</script>


<header class="navbar navbar-gitlab navbar-expand-sm js-navbar" data-qa-selector="navbar">
<a class="sr-only gl-accessibility" href="#content-body" tabindex="1">Skip to content</a>
<div class="container-fluid">
<div class="header-content">
<div class="title-container">
<h1 class="title">
<span class="gl-sr-only">GitLab</span>
<a title="Dashboard" id="logo" href="/"><svg width="24" height="24" class="tanuki-logo" viewBox="0 0 36 36">
  <path class="tanuki-shape tanuki-left-ear" fill="#e24329" d="M2 14l9.38 9v-9l-4-12.28c-.205-.632-1.176-.632-1.38 0z"/>
  <path class="tanuki-shape tanuki-right-ear" fill="#e24329" d="M34 14l-9.38 9v-9l4-12.28c.205-.632 1.176-.632 1.38 0z"/>
  <path class="tanuki-shape tanuki-nose" fill="#e24329" d="M18,34.38 3,14 33,14 Z"/>
  <path class="tanuki-shape tanuki-left-eye" fill="#fc6d26" d="M18,34.38 11.38,14 2,14 6,25Z"/>
  <path class="tanuki-shape tanuki-right-eye" fill="#fc6d26" d="M18,34.38 24.62,14 34,14 30,25Z"/>
  <path class="tanuki-shape tanuki-left-cheek" fill="#fca326" d="M2 14L.1 20.16c-.18.565 0 1.2.5 1.56l17.42 12.66z"/>
  <path class="tanuki-shape tanuki-right-cheek" fill="#fca326" d="M34 14l1.9 6.16c.18.565 0 1.2-.5 1.56L18 34.38z"/>
</svg>

<span class="logo-text d-none d-lg-block gl-ml-3">
<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 617 169"><path d="M315.26 2.97h-21.8l.1 162.5h88.3v-20.1h-66.5l-.1-142.4M465.89 136.95c-5.5 5.7-14.6 11.4-27 11.4-16.6 0-23.3-8.2-23.3-18.9 0-16.1 11.2-23.8 35-23.8 4.5 0 11.7.5 15.4 1.2v30.1h-.1m-22.6-98.5c-17.6 0-33.8 6.2-46.4 16.7l7.7 13.4c8.9-5.2 19.8-10.4 35.5-10.4 17.9 0 25.8 9.2 25.8 24.6v7.9c-3.5-.7-10.7-1.2-15.1-1.2-38.2 0-57.6 13.4-57.6 41.4 0 25.1 15.4 37.7 38.7 37.7 15.7 0 30.8-7.2 36-18.9l4 15.9h15.4v-83.2c-.1-26.3-11.5-43.9-44-43.9M557.63 149.1c-8.2 0-15.4-1-20.8-3.5V70.5c7.4-6.2 16.6-10.7 28.3-10.7 21.1 0 29.2 14.9 29.2 39 0 34.2-13.1 50.3-36.7 50.3m9.2-110.6c-19.5 0-30 13.3-30 13.3v-21l-.1-27.8h-21.3l.1 158.5c10.7 4.5 25.3 6.9 41.2 6.9 40.7 0 60.3-26 60.3-70.9-.1-35.5-18.2-59-50.2-59M77.9 20.6c19.3 0 31.8 6.4 39.9 12.9l9.4-16.3C114.5 6 97.3 0 78.9 0 32.5 0 0 28.3 0 85.4c0 59.8 35.1 83.1 75.2 83.1 20.1 0 37.2-4.7 48.4-9.4l-.5-63.9V75.1H63.6v20.1h38l.5 48.5c-5 2.5-13.6 4.5-25.3 4.5-32.2 0-53.8-20.3-53.8-63-.1-43.5 22.2-64.6 54.9-64.6M231.43 2.95h-21.3l.1 27.3v94.3c0 26.3 11.4 43.9 43.9 43.9 4.5 0 8.9-.4 13.1-1.2v-19.1c-3.1.5-6.4.7-9.9.7-17.9 0-25.8-9.2-25.8-24.6v-65h35.7v-17.8h-35.7l-.1-38.5M155.96 165.47h21.3v-124h-21.3v124M155.96 24.37h21.3V3.07h-21.3v21.3"/></svg>

</span>
</a></h1>
<ul class="list-unstyled navbar-sub-nav">
<li class="home"><a title="Projects" class="dashboard-shortcuts-projects" href="/explore">Projects
</a></li><li class=""><a title="Groups" class="dashboard-shortcuts-groups" href="/explore/groups">Groups
</a></li><li class=""><a title="Snippets" class="dashboard-shortcuts-snippets" href="/explore/snippets">Snippets
</a></li><li>
<a title="About GitLab CE" href="/help">Help</a>
</li>
</ul>

</div>
<div class="navbar-collapse collapse">
<ul class="nav navbar-nav">
<li class="nav-item d-none d-lg-block m-auto">
<div class="search search-form" data-track-event="activate_form_input" data-track-label="navbar_search" data-track-value="">
<form class="form-inline" action="/search" accept-charset="UTF-8" method="get"><input name="utf8" type="hidden" value="&#x2713;" /><div class="search-input-container">
<div class="search-input-wrap">
<div class="dropdown" data-url="/search/autocomplete">
<input type="search" name="search" id="search" placeholder="Search or jump to…" class="search-input dropdown-menu-toggle no-outline js-search-dashboard-options" spellcheck="false" tabindex="1" autocomplete="off" data-issues-path="/dashboard/issues" data-mr-path="/dashboard/merge_requests" data-qa-selector="search_term_field" aria-label="Search or jump to…" />
<button class="hidden js-dropdown-search-toggle" data-toggle="dropdown" type="button"></button>
<div class="dropdown-menu dropdown-select js-dashboard-search-options">
<div class="dropdown-content"><ul>
<li class="dropdown-menu-empty-item">
<a>
Loading...
</a>
</li>
</ul>
</div><div class="dropdown-loading"><i aria-hidden="true" data-hidden="true" class="fa fa-spinner fa-spin"></i></div>
</div>
<svg class="s16 search-icon" data-testid="search-icon"><use xlink:href="/assets/icons-1e863578ceb6844cc6941dadfd4b07001aed5876dc579fe61ea58ffd1458e7e8.svg#search"></use></svg>
<svg class="s16 clear-icon js-clear-input" data-testid="close-icon"><use xlink:href="/assets/icons-1e863578ceb6844cc6941dadfd4b07001aed5876dc579fe61ea58ffd1458e7e8.svg#close"></use></svg>
</div>
</div>
</div>
<input type="hidden" name="group_id" id="group_id" value="" class="js-search-group-options" />
<input type="hidden" name="project_id" id="search_project_id" value="681" class="js-search-project-options" data-project-path="coq-lmfi" data-name="coq-lmfi" data-issues-path="/letouzey/coq-lmfi/-/issues" data-mr-path="/letouzey/coq-lmfi/-/merge_requests" data-issues-disabled="false" />
<input type="hidden" name="scope" id="scope" />
<input type="hidden" name="search_code" id="search_code" value="true" />
<input type="hidden" name="snippets" id="snippets" value="false" />
<input type="hidden" name="repository_ref" id="repository_ref" value="master" />
<input type="hidden" name="nav_source" id="nav_source" value="navbar" />
<div class="search-autocomplete-opts hide" data-autocomplete-path="/search/autocomplete" data-autocomplete-project-id="681" data-autocomplete-project-ref="master"></div>
</form></div>

</li>
<li class="nav-item d-inline-block d-lg-none">
<a title="Search" aria-label="Search" data-toggle="tooltip" data-placement="bottom" data-container="body" href="/search?project_id=681"><svg class="s16" data-testid="search-icon"><use xlink:href="/assets/icons-1e863578ceb6844cc6941dadfd4b07001aed5876dc579fe61ea58ffd1458e7e8.svg#search"></use></svg>
</a></li>
<li class="nav-item header-help dropdown d-none d-md-block">
<a class="header-help-dropdown-toggle" data-toggle="dropdown" href="/help"><span class="gl-sr-only">
Help
</span>
<svg class="s16" data-testid="question-icon"><use xlink:href="/assets/icons-1e863578ceb6844cc6941dadfd4b07001aed5876dc579fe61ea58ffd1458e7e8.svg#question"></use></svg>
<svg class="s16 caret-down" data-testid="chevron-down-icon"><use xlink:href="/assets/icons-1e863578ceb6844cc6941dadfd4b07001aed5876dc579fe61ea58ffd1458e7e8.svg#chevron-down"></use></svg>
</a><div class="dropdown-menu dropdown-menu-right">
<ul>

<li>
<a href="/help">Help</a>
</li>
<li>
<a href="https://about.gitlab.com/getting-help/">Support</a>
</li>
<li>
<a target="_blank" class="text-nowrap" rel="noopener noreferrer" data-track-event="click_forum" data-track-property="question_menu" href="https://forum.gitlab.com/">Community forum</a>

</li>
<li>
<button class="js-shortcuts-modal-trigger" type="button">
Keyboard shortcuts
<span aria-hidden class="text-secondary float-right">?</span>
</button>
</li>
<li class="divider"></li>
<li>
<a href="https://about.gitlab.com/submit-feedback">Submit feedback</a>
</li>
<li>
<a target="_blank" class="text-nowrap" href="https://about.gitlab.com/contributing">Contribute to GitLab
</a>
</li>

</ul>

</div>
</li>
<li class="nav-item">
<div>
<a class="btn btn-sign-in" href="/users/sign_in?redirect_to_referer=yes">Sign in</a>
</div>
</li>
</ul>
</div>
<button class="navbar-toggler d-block d-sm-none" type="button">
<span class="sr-only">Toggle navigation</span>
<svg class="s12 more-icon js-navbar-toggle-right" data-testid="ellipsis_h-icon"><use xlink:href="/assets/icons-1e863578ceb6844cc6941dadfd4b07001aed5876dc579fe61ea58ffd1458e7e8.svg#ellipsis_h"></use></svg>
<svg class="s12 close-icon js-navbar-toggle-left" data-testid="close-icon"><use xlink:href="/assets/icons-1e863578ceb6844cc6941dadfd4b07001aed5876dc579fe61ea58ffd1458e7e8.svg#close"></use></svg>
</button>
</div>
</div>
</header>

<div class="layout-page page-with-contextual-sidebar">
<div class="nav-sidebar">
<div class="nav-sidebar-inner-scroll">
<div class="context-header">
<a title="coq-lmfi" href="/letouzey/coq-lmfi"><div class="avatar-container rect-avatar s40 project-avatar">
<div class="avatar s40 avatar-tile identicon bg3">C</div>
</div>
<div class="sidebar-context-title">
coq-lmfi
</div>
</a></div>
<ul class="sidebar-top-level-items qa-project-sidebar">
<li class="home"><a class="shortcuts-project rspec-project-link" data-qa-selector="project_link" href="/letouzey/coq-lmfi"><div class="nav-icon-container">
<svg class="s16" data-testid="home-icon"><use xlink:href="/assets/icons-1e863578ceb6844cc6941dadfd4b07001aed5876dc579fe61ea58ffd1458e7e8.svg#home"></use></svg>
</div>
<span class="nav-item-name">
Project overview
</span>
</a><ul class="sidebar-sub-level-items">
<li class="fly-out-top-item"><a href="/letouzey/coq-lmfi"><strong class="fly-out-top-item-name">
Project overview
</strong>
</a></li><li class="divider fly-out-top-item"></li>
<li class=""><a title="Project details" class="shortcuts-project" href="/letouzey/coq-lmfi"><span>Details</span>
</a></li><li class=""><a title="Activity" class="shortcuts-project-activity" data-qa-selector="activity_link" href="/letouzey/coq-lmfi/activity"><span>Activity</span>
</a></li><li class=""><a title="Releases" class="shortcuts-project-releases" href="/letouzey/coq-lmfi/-/releases"><span>Releases</span>
</a></li></ul>
</li><li class="active"><a class="shortcuts-tree" data-qa-selector="repository_link" href="/letouzey/coq-lmfi/-/tree/master"><div class="nav-icon-container">
<svg class="s16" data-testid="doc-text-icon"><use xlink:href="/assets/icons-1e863578ceb6844cc6941dadfd4b07001aed5876dc579fe61ea58ffd1458e7e8.svg#doc-text"></use></svg>
</div>
<span class="nav-item-name" id="js-onboarding-repo-link">
Repository
</span>
</a><ul class="sidebar-sub-level-items">
<li class="fly-out-top-item active"><a href="/letouzey/coq-lmfi/-/tree/master"><strong class="fly-out-top-item-name">
Repository
</strong>
</a></li><li class="divider fly-out-top-item"></li>
<li class="active"><a href="/letouzey/coq-lmfi/-/tree/master">Files
</a></li><li class=""><a id="js-onboarding-commits-link" href="/letouzey/coq-lmfi/-/commits/master">Commits
</a></li><li class=""><a data-qa-selector="branches_link" id="js-onboarding-branches-link" href="/letouzey/coq-lmfi/-/branches">Branches
</a></li><li class=""><a data-qa-selector="tags_link" href="/letouzey/coq-lmfi/-/tags">Tags
</a></li><li class=""><a href="/letouzey/coq-lmfi/-/graphs/master">Contributors
</a></li><li class=""><a href="/letouzey/coq-lmfi/-/network/master">Graph
</a></li><li class=""><a href="/letouzey/coq-lmfi/-/compare?from=master&amp;to=master">Compare
</a></li>
</ul>
</li><li class=""><a class="shortcuts-issues qa-issues-item" href="/letouzey/coq-lmfi/-/issues"><div class="nav-icon-container">
<svg class="s16" data-testid="issues-icon"><use xlink:href="/assets/icons-1e863578ceb6844cc6941dadfd4b07001aed5876dc579fe61ea58ffd1458e7e8.svg#issues"></use></svg>
</div>
<span class="nav-item-name" id="js-onboarding-issues-link">
Issues
</span>
<span class="badge badge-pill count issue_counter">
0
</span>
</a><ul class="sidebar-sub-level-items">
<li class="fly-out-top-item"><a href="/letouzey/coq-lmfi/-/issues"><strong class="fly-out-top-item-name">
Issues
</strong>
<span class="badge badge-pill count issue_counter fly-out-badge">
0
</span>
</a></li><li class="divider fly-out-top-item"></li>
<li class=""><a title="Issues" href="/letouzey/coq-lmfi/-/issues"><span>
List
</span>
</a></li><li class=""><a title="Boards" data-qa-selector="issue_boards_link" href="/letouzey/coq-lmfi/-/boards"><span>
Boards
</span>
</a></li><li class=""><a title="Labels" class="qa-labels-link" href="/letouzey/coq-lmfi/-/labels"><span>
Labels
</span>
</a></li><li class=""><a title="Service Desk" href="/letouzey/coq-lmfi/-/issues/service_desk">Service Desk
</a></li>
<li class=""><a title="Milestones" class="qa-milestones-link" href="/letouzey/coq-lmfi/-/milestones"><span>
Milestones
</span>
</a></li>
</ul>
</li><li class=""><a class="shortcuts-merge_requests" data-qa-selector="merge_requests_link" href="/letouzey/coq-lmfi/-/merge_requests"><div class="nav-icon-container">
<svg class="s16" data-testid="git-merge-icon"><use xlink:href="/assets/icons-1e863578ceb6844cc6941dadfd4b07001aed5876dc579fe61ea58ffd1458e7e8.svg#git-merge"></use></svg>
</div>
<span class="nav-item-name" id="js-onboarding-mr-link">
Merge Requests
</span>
<span class="badge badge-pill count merge_counter js-merge-counter">
0
</span>
</a><ul class="sidebar-sub-level-items is-fly-out-only">
<li class="fly-out-top-item"><a href="/letouzey/coq-lmfi/-/merge_requests"><strong class="fly-out-top-item-name">
Merge Requests
</strong>
<span class="badge badge-pill count merge_counter js-merge-counter fly-out-badge">
0
</span>
</a></li></ul>
</li>

<li class=""><a class="shortcuts-operations" data-qa-selector="operations_link" href="/letouzey/coq-lmfi/-/feature_flags"><div class="nav-icon-container">
<svg class="s16" data-testid="cloud-gear-icon"><use xlink:href="/assets/icons-1e863578ceb6844cc6941dadfd4b07001aed5876dc579fe61ea58ffd1458e7e8.svg#cloud-gear"></use></svg>
</div>
<span class="nav-item-name">
Operations
</span>
</a><ul class="sidebar-sub-level-items">
<li class="fly-out-top-item"><a href="/letouzey/coq-lmfi/-/feature_flags"><strong class="fly-out-top-item-name">
Operations
</strong>
</a></li><li class="divider fly-out-top-item"></li>
<li class=""><a title="Incidents" data-qa-selector="operations_incidents_link" href="/letouzey/coq-lmfi/-/incidents"><span>
Incidents
</span>
</a></li></ul>
</li><li class=""><a data-qa-selector="packages_link" href="/letouzey/coq-lmfi/-/packages"><div class="nav-icon-container">
<svg class="s16" data-testid="package-icon"><use xlink:href="/assets/icons-1e863578ceb6844cc6941dadfd4b07001aed5876dc579fe61ea58ffd1458e7e8.svg#package"></use></svg>
</div>
<span class="nav-item-name">
Packages &amp; Registries
</span>
</a><ul class="sidebar-sub-level-items">
<li class="fly-out-top-item"><a href="/letouzey/coq-lmfi/-/packages"><strong class="fly-out-top-item-name">
Packages &amp; Registries
</strong>
</a></li><li class="divider fly-out-top-item"></li>
<li class=""><a title="Package Registry" href="/letouzey/coq-lmfi/-/packages"><span>Package Registry</span>
</a></li></ul>
</li>
<li class=""><a data-qa-selector="analytics_anchor" href="/letouzey/coq-lmfi/-/value_stream_analytics"><div class="nav-icon-container">
<svg class="s16" data-testid="chart-icon"><use xlink:href="/assets/icons-1e863578ceb6844cc6941dadfd4b07001aed5876dc579fe61ea58ffd1458e7e8.svg#chart"></use></svg>
</div>
<span class="nav-item-name" data-qa-selector="analytics_link">
Analytics
</span>
</a><ul class="sidebar-sub-level-items" data-qa-selector="analytics_sidebar_submenu">
<li class="fly-out-top-item"><a href="/letouzey/coq-lmfi/-/value_stream_analytics"><strong class="fly-out-top-item-name">
Analytics
</strong>
</a></li><li class="divider fly-out-top-item"></li>
<li class=""><a class="shortcuts-repository-charts" title="Repository" href="/letouzey/coq-lmfi/-/graphs/master/charts"><span>Repository</span>
</a></li><li class=""><a class="shortcuts-project-cycle-analytics" title="Value Stream" href="/letouzey/coq-lmfi/-/value_stream_analytics"><span>Value Stream</span>
</a></li></ul>
</li>
<li class=""><a class="shortcuts-wiki" data-qa-selector="wiki_link" href="/letouzey/coq-lmfi/-/wikis/home"><div class="nav-icon-container">
<svg class="s16" data-testid="book-icon"><use xlink:href="/assets/icons-1e863578ceb6844cc6941dadfd4b07001aed5876dc579fe61ea58ffd1458e7e8.svg#book"></use></svg>
</div>
<span class="nav-item-name">
Wiki
</span>
</a><ul class="sidebar-sub-level-items is-fly-out-only">
<li class="fly-out-top-item"><a href="/letouzey/coq-lmfi/-/wikis/home"><strong class="fly-out-top-item-name">
Wiki
</strong>
</a></li></ul>
</li>
<li class=""><a class="shortcuts-snippets" data-qa-selector="snippets_link" href="/letouzey/coq-lmfi/-/snippets"><div class="nav-icon-container">
<svg class="s16" data-testid="snippet-icon"><use xlink:href="/assets/icons-1e863578ceb6844cc6941dadfd4b07001aed5876dc579fe61ea58ffd1458e7e8.svg#snippet"></use></svg>
</div>
<span class="nav-item-name">
Snippets
</span>
</a><ul class="sidebar-sub-level-items is-fly-out-only">
<li class="fly-out-top-item"><a href="/letouzey/coq-lmfi/-/snippets"><strong class="fly-out-top-item-name">
Snippets
</strong>
</a></li></ul>
</li><li class=""><a title="Members" class="qa-members-link" id="js-onboarding-members-link" href="/letouzey/coq-lmfi/-/project_members"><div class="nav-icon-container">
<svg class="s16" data-testid="users-icon"><use xlink:href="/assets/icons-1e863578ceb6844cc6941dadfd4b07001aed5876dc579fe61ea58ffd1458e7e8.svg#users"></use></svg>
</div>
<span class="nav-item-name">
Members
</span>
</a><ul class="sidebar-sub-level-items is-fly-out-only">
<li class="fly-out-top-item"><a href="/letouzey/coq-lmfi/-/project_members"><strong class="fly-out-top-item-name">
Members
</strong>
</a></li></ul>
</li><a class="toggle-sidebar-button js-toggle-sidebar qa-toggle-sidebar rspec-toggle-sidebar" role="button" title="Toggle sidebar" type="button">
<svg class="s16 icon-chevron-double-lg-left" data-testid="chevron-double-lg-left-icon"><use xlink:href="/assets/icons-1e863578ceb6844cc6941dadfd4b07001aed5876dc579fe61ea58ffd1458e7e8.svg#chevron-double-lg-left"></use></svg>
<svg class="s16 icon-chevron-double-lg-right" data-testid="chevron-double-lg-right-icon"><use xlink:href="/assets/icons-1e863578ceb6844cc6941dadfd4b07001aed5876dc579fe61ea58ffd1458e7e8.svg#chevron-double-lg-right"></use></svg>
<span class="collapse-text">Collapse sidebar</span>
</a>
<button name="button" type="button" class="close-nav-button"><svg class="s16" data-testid="close-icon"><use xlink:href="/assets/icons-1e863578ceb6844cc6941dadfd4b07001aed5876dc579fe61ea58ffd1458e7e8.svg#close"></use></svg>
<span class="collapse-text">Close sidebar</span>
</button>
<li class="hidden">
<a title="Activity" class="shortcuts-project-activity" href="/letouzey/coq-lmfi/activity"><span>
Activity
</span>
</a></li>
<li class="hidden">
<a title="Network" class="shortcuts-network" href="/letouzey/coq-lmfi/-/network/master">Graph
</a></li>
<li class="hidden">
<a class="shortcuts-new-issue" href="/letouzey/coq-lmfi/-/issues/new">Create a new issue
</a></li>
<li class="hidden">
<a title="Commits" class="shortcuts-commits" href="/letouzey/coq-lmfi/-/commits/master">Commits
</a></li>
<li class="hidden">
<a title="Issue Boards" class="shortcuts-issue-boards" href="/letouzey/coq-lmfi/-/boards">Issue Boards</a>
</li>
</ul>
</div>
</div>

<div class="content-wrapper">
<div class="mobile-overlay"></div>

<div class="alert-wrapper">













<nav class="breadcrumbs container-fluid container-limited" role="navigation">
<div class="breadcrumbs-container">
<button name="button" type="button" class="toggle-mobile-nav"><span class="sr-only">Open sidebar</span>
<svg class="s16" data-testid="hamburger-icon"><use xlink:href="/assets/icons-1e863578ceb6844cc6941dadfd4b07001aed5876dc579fe61ea58ffd1458e7e8.svg#hamburger"></use></svg>
</button><div class="breadcrumbs-links js-title-container" data-qa-selector="breadcrumb_links_content">
<ul class="list-unstyled breadcrumbs-list js-breadcrumbs-list">
<li><a href="/letouzey">Pierre Letouzey</a><svg class="s8 breadcrumbs-list-angle" data-testid="angle-right-icon"><use xlink:href="/assets/icons-1e863578ceb6844cc6941dadfd4b07001aed5876dc579fe61ea58ffd1458e7e8.svg#angle-right"></use></svg></li> <li><a href="/letouzey/coq-lmfi"><span class="breadcrumb-item-text js-breadcrumb-item-text">coq-lmfi</span></a><svg class="s8 breadcrumbs-list-angle" data-testid="angle-right-icon"><use xlink:href="/assets/icons-1e863578ceb6844cc6941dadfd4b07001aed5876dc579fe61ea58ffd1458e7e8.svg#angle-right"></use></svg></li>

<li>
<h2 class="breadcrumbs-sub-title"><a href="/letouzey/coq-lmfi/-/blob/master/2-preuves/other-provers/isabelle/IFOLBIS.thy">Repository</a></h2>
</li>
</ul>
</div>

</div>
</nav>

</div>
<div class="container-fluid container-limited ">
<div class="content" id="content-body">
<div class="flash-container flash-container-page sticky">
</div>

<div class="js-signature-container" data-signatures-path="/letouzey/coq-lmfi/-/commits/067199ea0405f3537bc76f51b0eb57ff9fc4fd59/signatures?limit=1"></div>

<div class="tree-holder" id="tree-holder">
<div class="nav-block">
<div class="tree-ref-container">
<div class="tree-ref-holder">
<form class="project-refs-form" action="/letouzey/coq-lmfi/-/refs/switch" accept-charset="UTF-8" method="get"><input name="utf8" type="hidden" value="&#x2713;" /><input type="hidden" name="destination" id="destination" value="blob" />
<input type="hidden" name="path" id="path" value="2-preuves/other-provers/isabelle/IFOLBIS.thy" />
<div class="dropdown">
<button class="dropdown-menu-toggle js-project-refs-dropdown qa-branches-select" type="button" data-toggle="dropdown" data-selected="master" data-ref="master" data-refs-url="/letouzey/coq-lmfi/refs?sort=updated_desc" data-field-name="ref" data-submit-form-on-click="true" data-visit="true"><span class="dropdown-toggle-text ">master</span><i aria-hidden="true" data-hidden="true" class="fa fa-chevron-down"></i></button>
<div class="dropdown-menu dropdown-menu-paging dropdown-menu-selectable git-revision-dropdown qa-branches-dropdown">
<div class="dropdown-page-one">
<div class="dropdown-title gl-display-flex"><span class="gl-ml-auto">Switch branch/tag</span><button class="dropdown-title-button dropdown-menu-close gl-ml-auto" aria-label="Close" type="button"><svg class="s16 dropdown-menu-close-icon" data-testid="close-icon"><use xlink:href="/assets/icons-1e863578ceb6844cc6941dadfd4b07001aed5876dc579fe61ea58ffd1458e7e8.svg#close"></use></svg></button></div>
<div class="dropdown-input"><input type="search" id="" class="dropdown-input-field qa-dropdown-input-field" placeholder="Search branches and tags" autocomplete="off" /><svg class="s16 dropdown-input-search" data-testid="search-icon"><use xlink:href="/assets/icons-1e863578ceb6844cc6941dadfd4b07001aed5876dc579fe61ea58ffd1458e7e8.svg#search"></use></svg><svg class="s16 dropdown-input-clear js-dropdown-input-clear" data-testid="close-icon"><use xlink:href="/assets/icons-1e863578ceb6844cc6941dadfd4b07001aed5876dc579fe61ea58ffd1458e7e8.svg#close"></use></svg></div>
<div class="dropdown-content"></div>
<div class="dropdown-loading"><i aria-hidden="true" data-hidden="true" class="fa fa-spinner fa-spin"></i></div>
</div>
</div>
</div>
</form>
</div>
<ul class="breadcrumb repo-breadcrumb">
<li class="breadcrumb-item">
<a href="/letouzey/coq-lmfi/-/tree/master">coq-lmfi
</a></li>
<li class="breadcrumb-item">
<a href="/letouzey/coq-lmfi/-/tree/master/2-preuves">2-preuves</a>
</li>
<li class="breadcrumb-item">
<a href="/letouzey/coq-lmfi/-/tree/master/2-preuves/other-provers">other-provers</a>
</li>
<li class="breadcrumb-item">
<a href="/letouzey/coq-lmfi/-/tree/master/2-preuves/other-provers/isabelle">isabelle</a>
</li>
<li class="breadcrumb-item">
<a href="/letouzey/coq-lmfi/-/blob/master/2-preuves/other-provers/isabelle/IFOLBIS.thy"><strong>IFOLBIS.thy</strong>
</a></li>
</ul>
</div>
<div class="tree-controls gl-children-ml-sm-3"><a class="btn shortcuts-find-file" rel="nofollow" href="/letouzey/coq-lmfi/-/find_file/master">Find file
</a><a class="btn js-blob-blame-link" href="/letouzey/coq-lmfi/-/blame/master/2-preuves/other-provers/isabelle/IFOLBIS.thy">Blame</a><a class="btn" href="/letouzey/coq-lmfi/-/commits/master/2-preuves/other-provers/isabelle/IFOLBIS.thy">History</a><a class="btn js-data-file-blob-permalink-url" href="/letouzey/coq-lmfi/-/blob/edcca26a8bdd206e1b9e47c29b211808b8e6ed03/2-preuves/other-provers/isabelle/IFOLBIS.thy">Permalink</a></div>
</div>

<div class="info-well d-none d-sm-block">
<div class="well-segment">
<ul class="blob-commit-info">
<li class="commit flex-row js-toggle-container" id="commit-067199ea">
<div class="avatar-cell d-none d-sm-block">
<a href="mailto:pierre.letouzey@inria.fr"><img alt="Pierre Letouzey&#39;s avatar" src="https://secure.gravatar.com/avatar/4db53e127028225c492d6da1f9d23602?s=80&amp;d=identicon" class="avatar s40 d-none d-sm-inline-block" title="Pierre Letouzey" /></a>
</div>
<div class="commit-detail flex-list">
<div class="commit-content qa-commit-content">
<a class="commit-row-message item-title js-onboarding-commit-item " href="/letouzey/coq-lmfi/-/commit/067199ea0405f3537bc76f51b0eb57ff9fc4fd59">fichiers repris du depot cours-preuves</a>
<span class="commit-row-message d-inline d-sm-none">
&middot;
067199ea
</span>
<div class="committer">
<a class="commit-author-link" href="mailto:pierre.letouzey@inria.fr">Pierre Letouzey</a> authored <time class="js-timeago" title="Jan 2, 2021 6:50pm" datetime="2021-01-02T17:50:52Z" data-toggle="tooltip" data-placement="bottom" data-container="body">Jan 02, 2021</time>
</div>

</div>
<div class="commit-actions flex-row">

<div class="js-commit-pipeline-status" data-endpoint="/letouzey/coq-lmfi/-/commit/067199ea0405f3537bc76f51b0eb57ff9fc4fd59/pipelines?ref=master"></div>
<div class="commit-sha-group d-none d-sm-flex">
<div class="label label-monospace monospace">
067199ea
</div>
<button class="btn btn btn-default" data-toggle="tooltip" data-placement="bottom" data-container="body" data-title="Copy commit SHA" data-class="btn btn-default" data-clipboard-text="067199ea0405f3537bc76f51b0eb57ff9fc4fd59" type="button" title="Copy commit SHA" aria-label="Copy commit SHA"><svg class="s16" data-testid="copy-to-clipboard-icon"><use xlink:href="/assets/icons-1e863578ceb6844cc6941dadfd4b07001aed5876dc579fe61ea58ffd1458e7e8.svg#copy-to-clipboard"></use></svg></button>

</div>
</div>
</div>
</li>

</ul>
</div>


</div>
<div class="blob-content-holder" id="blob-content-holder">
<article class="file-holder">
<div class="js-file-title file-title-flex-parent">
<div class="file-header-content">
<svg class="s16" data-testid="doc-text-icon"><use xlink:href="/assets/icons-1e863578ceb6844cc6941dadfd4b07001aed5876dc579fe61ea58ffd1458e7e8.svg#doc-text"></use></svg>
<strong class="file-title-name">
IFOLBIS.thy
</strong>
<button class="btn btn-clipboard btn-transparent" data-toggle="tooltip" data-placement="bottom" data-container="body" data-class="btn-clipboard btn-transparent" data-title="Copy file path" data-clipboard-text="{&quot;text&quot;:&quot;2-preuves/other-provers/isabelle/IFOLBIS.thy&quot;,&quot;gfm&quot;:&quot;`2-preuves/other-provers/isabelle/IFOLBIS.thy`&quot;}" type="button" title="Copy file path" aria-label="Copy file path"><svg class="s16" data-testid="copy-to-clipboard-icon"><use xlink:href="/assets/icons-1e863578ceb6844cc6941dadfd4b07001aed5876dc579fe61ea58ffd1458e7e8.svg#copy-to-clipboard"></use></svg></button>
<small class="mr-1">
1.62 KB
</small>
</div>

<div class="file-actions"><a class="btn btn-primary js-edit-blob ml-2  btn-sm" data-track-event="click_edit" data-track-label="Edit" href="/letouzey/coq-lmfi/-/edit/master/2-preuves/other-provers/isabelle/IFOLBIS.thy">Edit</a><a class="btn btn-primary ide-edit-button ml-2 btn-inverted btn-sm" data-track-event="click_edit_ide" data-track-label="Web IDE" data-track-property="secondary" href="/-/ide/project/letouzey/coq-lmfi/edit/master/-/2-preuves/other-provers/isabelle/IFOLBIS.thy">Web IDE</a><div class="btn-group ml-2" role="group">

</div><div class="btn-group ml-2" role="group">
<button class="btn btn btn-sm js-copy-blob-source-btn" data-toggle="tooltip" data-placement="bottom" data-container="body" data-class="btn btn-sm js-copy-blob-source-btn" data-title="Copy file contents" data-clipboard-target=".blob-content[data-blob-id=&#39;3b5961e3cc07464737f7387bb94ec6cb23711c11&#39;]" type="button" title="Copy file contents" aria-label="Copy file contents"><svg class="s16" data-testid="copy-to-clipboard-icon"><use xlink:href="/assets/icons-1e863578ceb6844cc6941dadfd4b07001aed5876dc579fe61ea58ffd1458e7e8.svg#copy-to-clipboard"></use></svg></button>
<a class="btn btn-sm has-tooltip" target="_blank" rel="noopener noreferrer" aria-label="Open raw" title="Open raw" data-container="body" href="/letouzey/coq-lmfi/-/raw/master/2-preuves/other-provers/isabelle/IFOLBIS.thy"><svg class="s16" data-testid="doc-code-icon"><use xlink:href="/assets/icons-1e863578ceb6844cc6941dadfd4b07001aed5876dc579fe61ea58ffd1458e7e8.svg#doc-code"></use></svg></a>
<a download="2-preuves/other-provers/isabelle/IFOLBIS.thy" class="btn btn-sm has-tooltip" target="_blank" rel="noopener noreferrer" aria-label="Download" title="Download" data-container="body" href="/letouzey/coq-lmfi/-/raw/master/2-preuves/other-provers/isabelle/IFOLBIS.thy?inline=false"><svg class="s16" data-testid="download-icon"><use xlink:href="/assets/icons-1e863578ceb6844cc6941dadfd4b07001aed5876dc579fe61ea58ffd1458e7e8.svg#download"></use></svg></a>

</div></div>
</div>



<div data-blob-data="theory IFOLBIS
imports Pure
begin

class &quot;term&quot;
default_sort &quot;term&quot; (* restrict all type variables to sort &quot;term&quot; *)

typedecl o

judgment
  Trueprop      :: &quot;o =&gt; prop&quot;                  (&quot;(_)&quot; 5)

axiomatization
  eq :: &quot;[&#39;a, &#39;a] =&gt; o&quot;  (infixl &quot;=&quot; 50)
where
  refl:         &quot;a=a&quot; and
  subst:        &quot;a=b \&lt;Longrightarrow&gt; P(a) \&lt;Longrightarrow&gt; P(b)&quot;

axiomatization
  False :: o and
  conj :: &quot;[o, o] =&gt; o&quot;  (infixr &quot;&amp;&quot; 35) and
  disj :: &quot;[o, o] =&gt; o&quot;  (infixr &quot;|&quot; 30) and
  imp :: &quot;[o, o] =&gt; o&quot;  (infixr &quot;--&gt;&quot; 25)
where
  conjI: &quot;[| P;  Q |] ==&gt; P&amp;Q&quot; and
  conjunct1: &quot;P&amp;Q ==&gt; P&quot; and
  conjunct2: &quot;P&amp;Q ==&gt; Q&quot; and

  disjI1: &quot;P ==&gt; P|Q&quot; and
  disjI2: &quot;Q ==&gt; P|Q&quot; and
  disjE: &quot;[| P|Q;  P ==&gt; R;  Q ==&gt; R |] ==&gt; R&quot; and

  impI: &quot;(P ==&gt; Q) ==&gt; P--&gt;Q&quot; and
  mp: &quot;[| P--&gt;Q;  P |] ==&gt; Q&quot; and

  FalseE: &quot;False ==&gt; P&quot;

(* lemma test : &quot;False = False&quot;
   refus car False est un o, incompatible avec un &#39;a dans term
*)

axiomatization
  All :: &quot;(&#39;a =&gt; o) =&gt; o&quot;  (binder &quot;ALL &quot; 10) and
  Ex :: &quot;(&#39;a =&gt; o) =&gt; o&quot;  (binder &quot;EX &quot; 10)
where
  allI: &quot;(!!x. P(x)) ==&gt; (ALL x. P(x))&quot; and
  spec: &quot;(ALL x. P(x)) ==&gt; P(x)&quot; and
  exI: &quot;P(x) ==&gt; (EX x. P(x))&quot; and
  exE: &quot;[| EX x. P(x);  !!x. P(x) ==&gt; R |] ==&gt; R&quot;

lemma conjE:
  assumes major: &quot;P &amp; Q&quot;
    and r: &quot;[| P; Q |] ==&gt; R&quot;
  shows R
  apply (rule r)
  apply (rule conjunct1)
   apply (rule major)
  apply (rule conjunct2)
   apply (rule major)
  done

lemma impE:
  assumes major: &quot;P --&gt; Q&quot;
    and p:P
  and r: &quot;Q ==&gt; R&quot;
  shows R
  apply (rule r)
  apply (rule mp)
  apply (rule major)
  apply (rule p) (* or (rule `P`) *)
  done

(* lemma test : &quot;ALL P. P --&gt; P&quot; (* pas de quantification sur les propositions *) *)
" data-is-ci-config-file="false" id="js-blob-toggle-graph-preview"></div>
<div class="blob-viewer" data-path="2-preuves/other-provers/isabelle/IFOLBIS.thy" data-type="simple" data-url="/letouzey/coq-lmfi/-/blob/master/2-preuves/other-provers/isabelle/IFOLBIS.thy?format=json&amp;viewer=simple">
<div class="text-center gl-mt-4 gl-mb-3">
<span class="gl-spinner gl-spinner-orange gl-spinner-md qa-spinner" aria-label="Loading"></span>
</div>

</div>


</article>
</div>

<div class="modal" id="modal-upload-blob">
<div class="modal-dialog modal-lg">
<div class="modal-content">
<div class="modal-header">
<h3 class="page-title">Replace IFOLBIS.thy</h3>
<button aria-label="Close" class="close" data-dismiss="modal" type="button">
<span aria-hidden>&times;</span>
</button>
</div>
<div class="modal-body">
<form class="js-quick-submit js-upload-blob-form" data-method="put" action="/letouzey/coq-lmfi/-/update/master/2-preuves/other-provers/isabelle/IFOLBIS.thy" accept-charset="UTF-8" method="post"><input name="utf8" type="hidden" value="&#x2713;" /><input type="hidden" name="_method" value="put" /><input type="hidden" name="authenticity_token" value="nV8F4o7OkCX8/4Nb3Zp8prZMYN7qmkIa8VNYdDfmxyZWs97UAYEhvZjedk4Tb4ZIt8vwltZcS8oEpoXsXIGUVA==" /><div class="dropzone">
<div class="dropzone-previews blob-upload-dropzone-previews">
<p class="dz-message light">
Attach a file by drag &amp; drop or <a class="markdown-selector" href="#">click to upload</a>
</p>
</div>
</div>
<br>
<div class="dropzone-alerts gl-alert gl-alert-danger gl-mb-5 data" style="display:none"></div>
<div class="form-group row commit_message-group">
<label class="col-form-label col-sm-2" for="commit_message-00be71b7d8ab26d608341652f46051d7">Commit message
</label><div class="col-sm-10">
<div class="commit-message-container">
<div class="max-width-marker"></div>
<textarea name="commit_message" id="commit_message-00be71b7d8ab26d608341652f46051d7" class="form-control js-commit-message" placeholder="Replace IFOLBIS.thy" required="required" rows="3">
Replace IFOLBIS.thy</textarea>
</div>
</div>
</div>

<input type="hidden" name="branch_name" id="branch_name" />
<input type="hidden" name="create_merge_request" id="create_merge_request" value="1" />
<input type="hidden" name="original_branch" id="original_branch" value="master" class="js-original-branch" />

<div class="form-actions">
<button name="button" type="button" class="btn gl-button btn-success btn-upload-file" id="submit-all"><i aria-hidden="true" data-hidden="true" class="fa fa-spin fa-spinner js-loading-icon hidden"></i>
Replace file
</button><a class="btn gl-button btn-cancel" data-dismiss="modal" href="#">Cancel</a>
<div class="inline gl-ml-3">
A new branch will be created in your fork and a new merge request will be started.
</div>

</div>
</form></div>
</div>
</div>
</div>

</div>


</div>
</div>
</div>
</div>


<script>
//<![CDATA[
if ('loading' in HTMLImageElement.prototype) {
  document.querySelectorAll('img.lazy').forEach(img => {
    img.loading = 'lazy';
    let imgUrl = img.dataset.src;
    // Only adding width + height for avatars for now
    if (imgUrl.indexOf('/avatar/') > -1 && imgUrl.indexOf('?') === -1) {
      const targetWidth = img.getAttribute('width') || img.width;
      imgUrl += `?width=${targetWidth}`;
    }
    img.src = imgUrl;
    img.removeAttribute('data-src');
    img.classList.remove('lazy');
    img.classList.add('js-lazy-loaded', 'qa-js-lazy-loaded');
  });
}

//]]>
</script>

</body>
</html>


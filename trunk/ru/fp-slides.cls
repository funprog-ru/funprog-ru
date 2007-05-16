\NeedsTeXFormat{LaTeX2e}
\ProvidesClass{fp-slides}
\LoadClass[10pt,portrait]{beamer}

\usetheme{Warsaw}

% uncomment second
% !!! rewrite on ifx
\newcommand{\maybepause}{}
%\newcommand{\maybepause}{\pause}

\newif\ifpdf 
\ifx\pdfoutput\undefined 
   \pdffalse % we are not running PDFLaTeX 
\else 
   \pdfoutput=1 % we are running PDFLaTeX 
   \pdftrue 
\fi

\ifpdf 
%    \RequirePackage[pdftex]{graphicx} 
%    \RequirePackage[a4paper,pdftex,unicode,colorlinks=true]{hyperref}
%    \pdfcompresslevel=9 
\else 
%    \RequirePackage{graphicx} 
%    \RequirePackage[a4paper,unicode,colorlinks=true]{hyperref}
\fi

\newcommand{\insertgraph}[3][]{%
\ifpdf%
  \includegraphics[#1]{#3}%
\else%
  \includegraphics[#1]{#2}%
\fi%
}

%
%\usepackage{type1cm}
% \RequirePackage{pscyr}
% \renewcommand{\rmdefault}{ftm} 
% \renewcommand{\ttdefault}{fer} 
% \renewcommand{\sfdefault}{far} 
\usepackage{mathtext}
%\RequirePackage[a4paper,hmargin={2cm,2cm},vmargin={2cm,2cm},nohead,twoside]{geometry}
%\RequirePackage[a4paper,hmargin={2.5cm,2cm},vmargin={2cm,2cm},nohead,twoside]{geometry}
\RequirePackage[T2A]{fontenc}
\RequirePackage[koi8-r]{inputenc}
\RequirePackage[russian]{babel}
%\RequirePackage{enumerate}
%\RequirePackage{indentfirst,amsmath,citehack,longtable}


\RequirePackage{alltt}
\RequirePackage{epsfig}
% \RequirePackage{notes}
\RequirePackage{fancybox}
\RequirePackage{amssymb}
\RequirePackage{listings}
\lstset{tabsize=2,language=ML}

%%%%% commands from original slides
\newcommand{\nat}{\mbox{$\protect\Bbb N$}}
\newcommand{\num}{\mbox{$\protect\Bbb Z$}}
\newcommand{\rat}{\mbox{$\protect\Bbb Q$}}
\newcommand{\real}{\mbox{$\protect\Bbb R$}}
\newcommand{\complex}{\mbox{$\protect\Bbb C$}}
\newcommand{\xxx}{\mbox{$\protect\Bbb X$}}


\newcommand{\True}{\top}
\newcommand{\False}{\bot}
\newcommand{\Not}{\neg}
\renewcommand{\And}{\wedge}
\newcommand{\Or}{\vee}
\newcommand{\Imp}{\Rightarrow}
\newcommand{\Iff}{\Leftrightarrow}

\newcommand{\lamb}[1]{\lambda #1.\:}
\newcommand{\eps}[1]{\varepsilon #1.\:}
\newcommand{\all}[1]{\forall #1.\:}
\newcommand{\ex}[1]{\exists #1.\:}
\newcommand{\exu}[1]{\exists! #1.\:}

\newcommand{\BA}{\begin{array}[t]{l}}
\newcommand{\EA}{\end{array}}

\newcommand\leb{\lbrack\!\lbrack}
\newcommand\reb{\rbrack\!\rbrack}
\newcommand{\sem}[1]{\leb #1 \reb}
\newcommand{\Union}{\cup}
\newcommand{\defeq}{\stackrel{\bigtriangleup}{=}}

\def\alphas{\mathrel{\mathop{\longrightarrow}\limits_{\alpha}}}
\def\betas{\mathrel{\mathop{\longrightarrow}\limits_{\beta}}}
\def\etas{\mathrel{\mathop{\longrightarrow}\limits_{\eta}}}
\def\goesto{\longrightarrow}

\DefineNamedColor{named}{Green}   {cmyk}{1,0,1,0}

% колонтитулы
% \usepackage{fancyhdr}
% \pagestyle{fancy}
% \fancyhf{}
% \fancyhead[L,C,R]{}
% \fancyfoot[LE,RO]{\thepage{}}
% \renewcommand{\headrulewidth}{0pt}
% \renewcommand{\footrulewidth}{0pt}

\parsep 0pt plus 1pt
\itemsep 0pt plus 1pt

% оформление подписей под плавающими объектами
% \usepackage{caption2}
%\captionstyle{indent}%
% \renewcommand\captionfont{\normalsize}%
%\setcaptionmargin{\leftmargin}
%\setlength\captionindent{\parindent}
% \renewcommand\captionlabeldelim{.}
% \onelinecaptionstrue

\renewcommand{\topfraction}{.9}
\renewcommand{\textfraction}{.1}
\renewcommand{\bottomfraction}{.9}
%\renewcommand{\floatpagefraction}{.9}
%\renewcommand{\dblfloatpagefraction}{\floatpagefraction}
\setcounter{topnumber}{4}
\setcounter{bottomnumber}{4}
\setcounter{totalnumber}{4}
\setlength{\floatsep}{8pt plus 2pt minus 2pt}
\setlength{\textfloatsep}{8pt plus 2pt minus 2pt}
\setlength{\intextsep}{12pt plus 2pt minus 2pt}

\AtBeginDocument{%
\selectlanguage{russian}%
\frenchspacing
\righthyphenmin=2
\sloppy
\author{Джон~Харрисон}
\institute{Университет Кембриджа}
\title{Введение в Функциональное программирование}
}

%\frame{
%  \frametitle{}
%
%  \begin{itemize}
%  \end{itemize}
%}


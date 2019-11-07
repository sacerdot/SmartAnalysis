if &cp | set nocp | endif
let s:cpo_save=&cpo
set cpo&vim
inoremap <silent> <SNR>30_AutoPairsReturn =AutoPairsReturn()
inoremap <silent> <C-Tab> =UltiSnips#ListSnippets()
inoremap <C-BS> dbi
nnoremap  :FZF
snoremap <silent>  c
xnoremap <silent> 	 :call UltiSnips#SaveLastVisualSelection()gvs
snoremap <silent> 	 :call UltiSnips#ExpandSnippet()
snoremap  "_c
map \S :call OCaml_switch(1)
map \s :call OCaml_switch(0)
vmap gx <Plug>NetrwBrowseXVis
nmap gx <Plug>NetrwBrowseX
vnoremap <silent> <Plug>NetrwBrowseXVis :call netrw#BrowseXVis()
nnoremap <silent> <Plug>NetrwBrowseX :call netrw#BrowseX(expand((exists("g:netrw_gx")? g:netrw_gx : '<cfile>')),netrw#CheckIfRemote())
snoremap <silent> <Del> c
snoremap <silent> <BS> c
snoremap <silent> <C-Tab> :call UltiSnips#ListSnippets()
inoremap  :FZF
inoremap <silent> 	 =UltiSnips#ExpandSnippet()
let &cpo=s:cpo_save
unlet s:cpo_save
set autoindent
set autoread
set background=dark
set backspace=indent,eol,start
set expandtab
set fileencodings=ucs-bom,utf-8,default,latin1
set helplang=it
set hidden
set hlsearch
set ignorecase
set incsearch
set laststatus=2
set nomodeline
set mouse=a
set path=**,.,/usr/include,,
set printoptions=paper:a4
set ruler
set runtimepath=~/.vim/bundle/ctrlp.vim,~/.vim,~/.vim/plugged/vim-polyglot/,~/.vim/plugged/ultisnips/,~/.vim/plugged/vim-snippets/,~/.vim/plugged/neotex/,~/.vim/plugged/oceanic-next/,~/.vim/plugged/vim-airline/,~/.vim/plugged/neomake/,~/.fzf/,~/.vim/plugged/auto-pairs/,/var/lib/vim/addons,/usr/share/vim/vimfiles,/usr/share/vim/vim81,/usr/share/vim/vimfiles/after,/var/lib/vim/addons/after,~/.vim/plugged/vim-polyglot/after,~/.vim/plugged/ultisnips/after,~/.vim/plugged/oceanic-next/after,~/.vim/after,~/.opam/4.06.1/share/merlin/vim
set shiftwidth=4
set noshowmode
set smartcase
set smartindent
set smarttab
set spelllang=it,en
set splitright
set suffixes=.bak,~,.swp,.o,.info,.aux,.log,.dvi,.bbl,.blg,.brf,.cb,.ind,.idx,.ilg,.inx,.out,.toc
set tabstop=4
set termguicolors
set wildignorecase
set wildmenu
" vim: set ft=vim :

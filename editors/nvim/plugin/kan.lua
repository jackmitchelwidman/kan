-- Kan filetype registration (modern, load-order-independent). This works under
-- lazy.nvim and packer as well as native packages; the ftdetect/kan.vim autocmd
-- is kept as a fallback for older setups. Highlighting is in syntax/kan.vim.
vim.filetype.add({ extension = { kan = "kan" } })

;; ===== lando mode
(defvar lando-mode-hook nil)
(defvar lando-mode-map
  (let ((lando-mode-map (make-keymap)))
    (define-key lando-mode-map "\C-j" 'newline-and-indent)
    lando-mode-map)
  "Keymap for LANDO major mode")

(add-to-list 'auto-mode-alist '("\\.lando\\'" . lando-mode))

(defconst lando-font-lock-keywords-1
  (list 
   '("\\<system\\>" . font-lock-builtin-face)
   '("\\<subsystem\\>" . font-lock-builtin-face)
   '("\\<component\\>" . font-lock-builtin-face)
   '("\\<events\\>" . font-lock-builtin-face)
   '("\\<scenarios\\>" . font-lock-builtin-face)
   '("\\<requirements\\>" . font-lock-builtin-face)
   '("\\<relation\\>" . font-lock-builtin-face)
   '("\\<indexing\\>" . font-lock-builtin-face)
   '("\\<inherit\\>" . font-lock-builtin-face)
   '("\\<client\\>" . font-lock-builtin-face)
   '("\\<contains\\>" . font-lock-builtin-face)
  ) 
  "Minimal highlighting expressions for LANDO mode.")

(defvar lando-font-lock-keywords lando-font-lock-keywords-1 "Default highlighting expressions for LANDO mode.")

(defun lando-mode ()
  (interactive)
  (kill-all-local-variables)
  (use-local-map lando-mode-map)
  ;; Set up font-lock
  (set (make-local-variable 'font-lock-defaults) '(lando-font-lock-keywords))
  (setq major-mode 'lando-mode)
  (setq mode-name "LANDO")
  (run-hooks 'lando-mode-hook))

(provide 'lando-mode)
;; ===== end of lando-mode

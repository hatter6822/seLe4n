# seLe4n — Language Support / 语言支持 / Soporte de idiomas

<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="../../assets/logo_dark.png" />
    <img src="../../assets/logo.png" alt="seLe4n logo" width="120" />
  </picture>
</p>

<p align="center">
  <strong>seLe4n</strong> — A production-oriented microkernel in Lean 4 with machine-checked proofs
</p>

---

## Available Languages / 可用语言 / Idiomas disponibles

| Language | Native Name | README | Contributing | Quick Start |
|----------|-------------|--------|-------------|-------------|
| English | English | [README](../../README.md) | [CONTRIBUTING](../../CONTRIBUTING.md) | [Quick Start](../../README.md#quick-start) |
| 简体中文 | Chinese (Simplified) | [自述文件](zh-CN/README.md) | [贡献指南](zh-CN/CONTRIBUTING.md) | [快速入门](zh-CN/QUICKSTART.md) |
| Español | Spanish | [LÉAME](es/README.md) | [Contribuir](es/CONTRIBUTING.md) | [Inicio rápido](es/QUICKSTART.md) |
| 日本語 | Japanese | [はじめに](ja/README.md) | [貢献ガイド](ja/CONTRIBUTING.md) | [クイックスタート](ja/QUICKSTART.md) |
| 한국어 | Korean | [소개](ko/README.md) | [기여 가이드](ko/CONTRIBUTING.md) | [빠른 시작](ko/QUICKSTART.md) |
| العربية | Arabic | [اقرأني](ar/README.md) | [دليل المساهمة](ar/CONTRIBUTING.md) | [البداية السريعة](ar/QUICKSTART.md) |
| Français | French | [LISEZMOI](fr/README.md) | [Contribuer](fr/CONTRIBUTING.md) | [Démarrage rapide](fr/QUICKSTART.md) |
| Português | Portuguese (Brazil) | [LEIAME](pt-BR/README.md) | [Contribuir](pt-BR/CONTRIBUTING.md) | [Início rápido](pt-BR/QUICKSTART.md) |
| Русский | Russian | [ПРОЧТИМЕНЯ](ru/README.md) | [Руководство](ru/CONTRIBUTING.md) | [Быстрый старт](ru/QUICKSTART.md) |
| Deutsch | German | [LIESMICH](de/README.md) | [Mitwirken](de/CONTRIBUTING.md) | [Schnellstart](de/QUICKSTART.md) |
| हिन्दी | Hindi | [परिचय](hi/README.md) | [योगदान गाइड](hi/CONTRIBUTING.md) | [त्वरित प्रारंभ](hi/QUICKSTART.md) |

---

## Translation Guidelines

### For translators

- **Technical terms** (e.g., "microkernel", "capability", "invariant", "theorem") should remain in English or include the English term in parentheses after the translated term, as these are standard computer science terminology.
- **Code snippets, file paths, and command-line examples** must remain in English — they are functional and must not be translated.
- **Project-specific names** (seLe4n, seL4, Lean 4, Lake, Robin Hood hash table) must not be translated.
- Translations should be **natural and idiomatic** in the target language, not word-for-word calques.
- Each translation should include a link back to the English original for reference.

### Adding a new language

1. Create a new directory under `docs/i18n/<language-code>/`
2. Translate `README.md`, `CONTRIBUTING.md`, and `QUICKSTART.md`
3. Add the language to the table above
4. Add the language to the selector in the main `README.md`
5. Update `scripts/website_link_manifest.txt` with new paths
6. Submit a PR with the translations

### Translation status

All translations are community-maintained. If you find errors or sections that
need updating, please open a PR or issue.

Last synchronized with English sources: v0.18.6

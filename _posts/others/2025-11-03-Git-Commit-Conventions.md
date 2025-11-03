---
layout: post
title: "Git提交规范"
subtitle: "Git提交规范关键词说明"
date: 2025-11-03
author: "Wenqin"
tags: [other, 实用]
---
# Git 提交规范关键词说明

在使用 Git 进行版本控制时，遵循提交信息规范可以提高代码的可读性和维护效率。以下是常见的提交前缀（关键词）及其含义：

| 关键词   | 含义说明                                 | 示例                                      |
|----------|------------------------------------------|-------------------------------------------|
| `feat`   | 表示新增功能。                           | `feat: 增加用户注册功能`                  |
| `fix`    | 表示修复 Bug。                           | `fix: 修复登录页面崩溃的问题`             |
| `docs`   | 表示文档更新（不影响代码逻辑）。         | `docs: 更新 README 文件`                  |
| `style`  | 表示代码格式的修改，不影响逻辑。         | `style: 删除多余的空行`                   |
| `refactor` | 表示代码重构，不涉及功能新增或 Bug 修复。 | `refactor: 重构用户验证逻辑`              |
| `perf`   | 表示性能优化。                           | `perf: 优化图片加载速度`                  |
| `test`   | 表示测试相关的更改。                     | `test: 增加用户模块的单元测试`            |
| `chore`  | 表示构建过程或辅助工具的变动。           | `chore: 更新依赖库`                       |
| `build`  | 表示构建系统或外部依赖项的变更。         | `build: 升级 webpack 到版本 5`            |
| `ci`     | 表示持续集成配置的变更。                 | `ci: 修改 GitHub Actions 配置文件`        |
| `revert` | 表示回滚之前的提交。                     | `revert: 回滚 feat: 增加用户注册功能`     |

> **提示**：以上规范基于 [Conventional Commits](https://www.conventionalcommits.org/) 标准，适用于大多数现代前端/后端项目。

## 优势

- 使项目变更历史更加清晰；
- 便于团队成员快速理解每次提交的目的；
- 支持自动化工具（如生成 CHANGELOG、语义化版本发布等）解析提交记录。

建议在项目中通过工具（如 [commitlint](https://commitlint.js.org/) + [Husky](https://typicode.github.io/husky/)）强制校验提交信息格式，以确保规范落地。
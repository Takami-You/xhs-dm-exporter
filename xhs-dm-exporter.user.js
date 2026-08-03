// ==UserScript==
// @name         Xiaohongshu DM Exporter 小红书私信导出助手
// @namespace    https://github.com/Takami-You/xhs-dm-exporter
// @version      1.3.1
// @description  自动向上加载并导出当前小红书私信会话；支持正文、引用、表情、图片链接、时间分隔和可选内嵌图片。
// @author       咻咔咻咔咻
// @match        https://*.xiaohongshu.com/*
// @run-at       document-idle
// @grant        GM_download
// @grant        GM_xmlhttpRequest
// @connect      xiaohongshu.com
// @connect      xhscdn.com
// @connect      xhscdn.net
// @license      GPL-3.0
// ==/UserScript==

(() => {
  'use strict';

  const VERSION = '1.3.1';
  const GLOBAL_NAME = 'XHS_DM_EXPORTER';
  const DEFAULTS = {
    scrollContainerSelector: '',
    myName: '',
    otherName: '',
    settleMs: 90,
    mutationWaitMs: 420,
    maxRounds: 3000,
    stableRoundsToFinish: 3,
    scrollRatio: 6,
    fastJumpToTop: true,
    imageConcurrency: 3,
    parseChunkSize: 100,
    statusUpdateMs: 800,
    historyIdleMs: 12000,
    resourceRetries: 5,
    preferBrowserCache: true,
    selectors: {
      message: [
        '[data-message-id]',
        '.chat-item[data-message-id]',
        '.chat-item',
        '[class*="message-item"]',
        '[class*="messageItem"]'
      ],
      timeSeparator: [
        '.xhs-im-msg-list__time-divider',
        '.time-divider', '.time-separator', '.time-line', '.time',
        '[class*="time-divider"]', '[class*="time-separator"]',
        '[class*="timeDivider"]', '[class*="timeSeparator"]'
      ],
      content: [
        '.message-content', '.msg-content', '.content', '.text',
        '[class*="message-content"]', '[class*="messageContent"]',
        '[class*="msg-content"]', '[class*="bubble"]'
      ],
      quote: [
        '.chat-item__ref',
        '.quote', '.quoted-message', '.reply-content', '.reference',
        '.chat-item__quote', '.chat-item__reference', '.xhs-im-bubble-quote',
        '[class*="quote"]', '[class*="quoted"]', '[class*="reply-content"]',
        '[class*="replyContent"]', '[class*="reference"]', '[class*="refer"]'
      ],
      avatar: [
        '.avatar', 'img[class*="avatar"]', '[class*="avatar"] img'
      ]
    }
  };

  if (window[GLOBAL_NAME]?.version) {
    window[GLOBAL_NAME].showPanel?.();
    console.info(`[${GLOBAL_NAME}] 已加载 v${window[GLOBAL_NAME].version}`);
    return;
  }

  const state = {
    config: structuredCloneSafe(DEFAULTS),
    running: false,
    operation: null,
    stopRequested: false,
    messages: new Map(),
    timeline: [],
    markers: new Map(),
    seenRealIds: 0,
    rounds: 0,
    stableRounds: 0,
    errors: [],
    nodeMessageIds: new WeakMap(),
    nodeMarkerIds: new WeakMap(),
    markerSerial: 0,
    parsedNodeCount: 0,
    timelineMergeCount: 0,
    visualMediaUrls: new Set(),
    videoUrls: new Set(),
    lastCollectStatusAt: 0,
    container: null,
    startedAt: null,
    finishedAt: null,
    conversationTitle: '',
    participants: { me: '我', other: '对方' },
    panel: null,
    statusEl: null,
    detailEl: null,
    buttons: {},
    lastDirection: 'up'
  };

  function structuredCloneSafe(value) {
    try { return structuredClone(value); }
    catch (_) { return JSON.parse(JSON.stringify(value)); }
  }

  function mergeConfig(base, extra = {}) {
    const merged = structuredCloneSafe(base);
    for (const [key, value] of Object.entries(extra || {})) {
      if (key === 'selectors' && value && typeof value === 'object') {
        merged.selectors = { ...merged.selectors, ...value };
      } else if (value !== undefined) {
        merged[key] = value;
      }
    }
    for (const key of Object.keys(merged.selectors)) {
      const value = merged.selectors[key];
      merged.selectors[key] = Array.isArray(value) ? value.filter(Boolean) : [value].filter(Boolean);
    }
    return merged;
  }

  function selectorList(items) {
    return (items || []).filter(Boolean).join(',');
  }

  function safeQueryAll(root, selectors) {
    if (!root) return [];
    const result = [];
    for (const selector of selectors || []) {
      try { result.push(...root.querySelectorAll(selector)); }
      catch (error) { recordError(`无效选择器 ${selector}`, error); }
    }
    return [...new Set(result)];
  }

  function cleanText(value) {
    return String(value || '')
      .replace(/[\u200B-\u200D\uFEFF]/g, '')
      .replace(/\r/g, '')
      .replace(/[ \t]+\n/g, '\n')
      .replace(/\n[ \t]+/g, '\n')
      .replace(/\n{3,}/g, '\n\n')
      .replace(/[ \t]{2,}/g, ' ')
      .trim();
  }

  function hashString(input) {
    let hash = 2166136261;
    const str = String(input || '');
    for (let i = 0; i < str.length; i += 1) {
      hash ^= str.charCodeAt(i);
      hash = Math.imul(hash, 16777619);
    }
    return (hash >>> 0).toString(36);
  }

  function attrFirst(el, names) {
    for (const name of names) {
      const value = el?.getAttribute?.(name);
      if (value) return value;
    }
    return '';
  }

  function isElementVisible(el) {
    if (!(el instanceof Element)) return false;
    const style = getComputedStyle(el);
    if (style.display === 'none' || style.visibility === 'hidden') return false;
    const rect = el.getBoundingClientRect();
    return rect.width > 0 || rect.height > 0;
  }

  function getScrollCandidates() {
    const all = [document.scrollingElement, ...document.querySelectorAll('main,section,div,ul')]
      .filter(Boolean);
    return [...new Set(all)].filter((el) => {
      try {
        const style = getComputedStyle(el);
        const scrollable = /(auto|scroll|overlay)/.test(style.overflowY) || el === document.scrollingElement;
        return scrollable && el.clientHeight >= 180 && el.scrollHeight > el.clientHeight + 80;
      } catch (_) { return false; }
    });
  }

  function scoreContainer(el) {
    const messageMatches = safeQueryAll(el, state.config.selectors.message).length;
    const idMatches = el.querySelectorAll?.('[data-message-id]')?.length || 0;
    const classHint = /chat|message|conversation|im|scroll/i.test(`${el.id} ${el.className}`) ? 8 : 0;
    const sizeScore = Math.min(12, Math.log2(Math.max(2, el.scrollHeight / Math.max(1, el.clientHeight))) * 3);
    return messageMatches * 12 + idMatches * 18 + classHint + sizeScore;
  }

  function findScrollContainer() {
    const manual = state.config.scrollContainerSelector;
    if (manual) {
      try {
        const selected = document.querySelector(manual);
        if (selected) return selected;
      } catch (error) { recordError('指定的滚动容器选择器无效', error); }
    }
    const ranked = getScrollCandidates()
      .map((el) => ({ el, score: scoreContainer(el) }))
      .sort((a, b) => b.score - a.score);
    return ranked[0]?.score > 0 ? ranked[0].el : null;
  }

  function looksLikeTime(text) {
    const value = cleanText(text);
    if (!value || value.length > 50) return false;
    return /^(?:刚刚|昨天|今天|前天|周[一二三四五六日天]|星期[一二三四五六日天])?(?:\s*[上下中]午)?\s*(?:\d{1,4}[年./-])?(?:\d{1,2}[月./-])?(?:\d{1,2}日?)?(?:\s+|^)?\d{1,2}:\d{2}(?::\d{2})?$/.test(value)
      || /^\d{4}年\d{1,2}月\d{1,2}日/.test(value)
      || /^(?:今天|昨天|前天|刚刚)$/.test(value);
  }

  function getMessageNodes(container) {
    const xhsNodes = [...container.querySelectorAll('.chat-item')];
    const all = (xhsNodes.length ? xhsNodes : safeQueryAll(container, state.config.selectors.message))
      .filter((node) => node instanceof Element && (node.hasAttribute('data-message-id') || isElementVisible(node)));
    return all.filter((node) => {
      if (!node.hasAttribute('data-message-id') && node.querySelector('[data-message-id]')) return false;
      const text = cleanText(node.innerText || node.textContent);
      if (!node.hasAttribute('data-message-id') && looksLikeTime(text) && text.length < 50) return false;
      const classText = `${node.className || ''}`;
      const hasMessageHint = /chat-item|message|msg|bubble|left|right|incoming|outgoing/i.test(classText);
      const hasContent = text || node.querySelector('img,picture,video,[style*="background-image"]');
      return node.hasAttribute('data-message-id') || (hasMessageHint && hasContent);
    });
  }

  function getTimeSeparatorNodes(container, messageNodes) {
    const messages = new Set(messageNodes);
    const xhsNodes = [...container.querySelectorAll('.xhs-im-msg-list__time-divider')];
    return (xhsNodes.length ? xhsNodes : safeQueryAll(container, state.config.selectors.timeSeparator))
      .filter((node) => {
        if (!isElementVisible(node)) return false;
        const parentMessage = node.closest('[data-message-id],.chat-item');
        if (parentMessage && messages.has(parentMessage)) return false;
        return looksLikeTime(node.innerText || node.textContent);
      });
  }

  function sortDomOrder(nodes) {
    return [...new Set(nodes)].sort((a, b) => {
      if (a === b) return 0;
      const position = a.compareDocumentPosition(b);
      if (position & Node.DOCUMENT_POSITION_FOLLOWING) return -1;
      if (position & Node.DOCUMENT_POSITION_PRECEDING) return 1;
      return 0;
    });
  }

  function absoluteUrl(value) {
    if (!value) return '';
    try { return new URL(value, location.href).href; }
    catch (_) { return value; }
  }

  function bestSrcset(srcset) {
    if (!srcset) return '';
    const choices = srcset.split(',').map((entry) => {
      const parts = entry.trim().split(/\s+/);
      const descriptor = parts[1] || '1x';
      const weight = descriptor.endsWith('w') ? parseFloat(descriptor) : parseFloat(descriptor) * 1000;
      return { url: parts[0], weight: Number.isFinite(weight) ? weight : 0 };
    }).filter((entry) => entry.url);
    choices.sort((a, b) => b.weight - a.weight);
    return choices[0]?.url || '';
  }

  function extractUrlFromStyle(el) {
    const inline = el.getAttribute('style') || '';
    const computed = getComputedStyle(el).backgroundImage || '';
    const match = `${inline} ${computed}`.match(/url\(["']?([^"')]+)["']?\)/i);
    return absoluteUrl(match?.[1] || '');
  }

  function imageInfo(img, messageNode) {
    const original = attrFirst(img, [
      'data-origin-src', 'data-original-src', 'data-original', 'data-origin',
      'data-src', 'data-lazy-src'
    ]);
    const srcset = bestSrcset(img.getAttribute('srcset') || img.parentElement?.querySelector('source[srcset]')?.getAttribute('srcset'));
    const displayed = img.currentSrc || img.getAttribute('src') || '';
    const url = absoluteUrl(original || srcset || displayed);
    const thumb = absoluteUrl(displayed || srcset || original);
    const classText = `${img.className || ''} ${img.parentElement?.className || ''}`;
    const avatarRoot = safeQueryAll(messageNode, state.config.selectors.avatar);
    const isCardAsset = Boolean(img.closest('.xhs-im-bubble-card-note,.xhs-im-bubble__card-comment'));
    const isAvatar = !isCardAsset && avatarRoot.some((avatar) => avatar === img || avatar.contains(img));
    const width = img.naturalWidth || img.width || img.getBoundingClientRect().width;
    const height = img.naturalHeight || img.height || img.getBoundingClientRect().height;
    const alt = cleanText(img.alt || img.title || '');
    const isDefinitelyImage = /bubble__image|media-wrapper|note-cover|author-avatar/i.test(classText) || /^(?:图片消息|图片|照片)$/i.test(alt);
    const isEmoji = !isAvatar && !isDefinitelyImage && (/emoji|emoticon|sticker/i.test(classText) || ((width <= 72 && height <= 72) && Boolean(alt)));
    return { url, thumbnailUrl: thumb, alt, width: width || null, height: height || null, isAvatar, isEmoji, isCardAsset };
  }

  function extractMedia(messageNode) {
    const images = [];
    const emojis = [];
    for (const img of messageNode.querySelectorAll('img')) {
      const info = imageInfo(img, messageNode);
      if (!info.url || info.isAvatar || info.isCardAsset || info.url.startsWith('data:')) continue;
      const target = info.isEmoji ? emojis : images;
      if (!target.some((item) => item.url === info.url)) {
        target.push({
          url: info.url,
          thumbnailUrl: info.thumbnailUrl || info.url,
          alt: info.alt,
          width: info.width,
          height: info.height
        });
      }
    }
    for (const el of messageNode.querySelectorAll('[style*="background-image"]')) {
      const url = extractUrlFromStyle(el);
      if (url && !images.some((item) => item.url === url)) {
        images.push({ url, thumbnailUrl: url, alt: '', width: null, height: null });
      }
    }
    return { images, emojis };
  }

  function extractVideos(messageNode) {
    const videos = [];
    const add = (video) => {
      if (!video.url && !video.posterUrl) return;
      if (!videos.some((item) => item.url === video.url && item.posterUrl === video.posterUrl)) videos.push(video);
    };
    for (const video of messageNode.querySelectorAll('video')) {
      const source = video.currentSrc || attrFirst(video, ['src', 'data-src', 'data-url']) || video.querySelector('source[src]')?.getAttribute('src');
      add({
        url: absoluteUrl(source),
        posterUrl: absoluteUrl(attrFirst(video, ['poster', 'data-poster', 'data-cover'])),
        mimeType: video.querySelector('source[type]')?.getAttribute('type') || '',
        duration: Number.isFinite(video.duration) ? video.duration : null
      });
    }
    for (const node of messageNode.querySelectorAll('[class*="video"],[data-video-url],[data-play-url]')) {
      if (node.closest('.xhs-im-bubble-card-note-video-icon')) continue;
      const source = attrFirst(node, ['data-video-url', 'data-play-url', 'data-url', 'data-src', 'src']);
      const poster = attrFirst(node, ['poster', 'data-poster', 'data-cover']) || node.querySelector('img')?.currentSrc || node.querySelector('img')?.getAttribute('src');
      if (source && /(?:\.mp4|\.webm|\.mov|\.m3u8)(?:$|\?)/i.test(source)) {
        add({ url: absoluteUrl(source), posterUrl: absoluteUrl(poster), mimeType: '', duration: null });
      }
    }
    return videos;
  }

  function mediaItemFromImage(img, root) {
    if (!img) return null;
    const info = imageInfo(img, root);
    if (!info.url || info.url.startsWith('data:')) return null;
    return {
      url: info.url,
      thumbnailUrl: info.thumbnailUrl || info.url,
      alt: info.alt,
      width: info.width,
      height: info.height
    };
  }

  function extractNoteCards(root) {
    const cards = [];
    for (const cardRoot of root.querySelectorAll('.xhs-im-bubble-card-note')) {
      const title = cleanText(cardRoot.querySelector('.xhs-im-bubble-card-note-title')?.innerText || '');
      const author = cleanText(cardRoot.querySelector('.xhs-im-bubble-card-note-author-name')?.innerText || '');
      const cover = mediaItemFromImage(cardRoot.querySelector('.xhs-im-bubble-card-note-cover'), cardRoot);
      const authorAvatar = mediaItemFromImage(cardRoot.querySelector('.xhs-im-bubble-card-note-author-avatar'), cardRoot);
      const anchor = cardRoot.closest('a[href]') || cardRoot.querySelector('a[href]');
      const href = absoluteUrl(anchor?.getAttribute('href') || attrFirst(cardRoot, ['data-href', 'data-url', 'data-link']));
      const isVideo = Boolean(cardRoot.querySelector('.xhs-im-bubble-card-note-video-icon'));
      if (title || author || cover) {
        cards.push({ type: 'note', title, author, cover, authorAvatar, href: href || null, isVideo });
      }
    }
    for (const cardRoot of root.querySelectorAll('.xhs-im-bubble__card-comment')) {
      const label = cleanText(cardRoot.querySelector('.xhs-im-bubble__card-comment-label')?.innerText || '分享评论');
      const text = cleanText(cardRoot.querySelector('.xhs-im-bubble__card-comment-text')?.innerText || '');
      const cover = mediaItemFromImage(cardRoot.querySelector('.xhs-im-bubble__card-comment-note-cover'), cardRoot);
      const title = cleanText(cardRoot.querySelector('.xhs-im-bubble__card-comment-note-title')?.innerText || '');
      const from = cleanText(cardRoot.querySelector('.xhs-im-bubble__card-comment-note-from')?.innerText || '来自笔记');
      const anchor = cardRoot.closest('a[href]') || cardRoot.querySelector('a[href]');
      const href = absoluteUrl(anchor?.getAttribute('href') || attrFirst(cardRoot, ['data-href', 'data-url', 'data-link']));
      cards.push({ type: 'comment', label, text, title, from, cover, href: href || null });
    }
    return cards;
  }

  function detectSender(messageNode, container) {
    const descendants = [...messageNode.querySelectorAll('[class*="chat-item__content--"],[class*="chat-item__bubble--"]')]
      .map((node) => String(node.className || '').toLowerCase()).join(' ');
    if (/chat-item__content--right|chat-item__bubble--me/.test(descendants)) return 'me';
    if (/chat-item__content--left|chat-item__bubble--other/.test(descendants)) return 'other';
    let current = messageNode;
    for (let depth = 0; current && current !== container && depth < 4; depth += 1, current = current.parentElement) {
      const classes = ` ${String(current.className || '').toLowerCase().replace(/[_-]/g, ' ')} `;
      if (/\b(right|outgoing|mine|myself|self|sent)\b/.test(classes)) return 'me';
      if (/\b(left|incoming|other|received|receiver)\b/.test(classes)) return 'other';
    }
    try {
      const candidate = safeQueryAll(messageNode, state.config.selectors.content)[0] || messageNode;
      const rect = candidate.getBoundingClientRect();
      const parentRect = container.getBoundingClientRect();
      if (rect.width > 0 && parentRect.width > 0) {
        const center = rect.left + rect.width / 2;
        const ratio = (center - parentRect.left) / parentRect.width;
        if (ratio >= 0.62) return 'me';
        if (ratio <= 0.38) return 'other';
      }
    } catch (_) { /* ignore layout fallback */ }
    return 'unknown';
  }

  function isSystemMessage(messageNode, sender) {
    if (sender !== 'unknown') return false;
    const classes = `${messageNode.className || ''} ${[...messageNode.querySelectorAll('[class]')].slice(0, 20).map((node) => node.className).join(' ')}`;
    const text = cleanText(messageNode.innerText || messageNode.textContent);
    const hasAvatar = Boolean(messageNode.querySelector('.chat-item__avatar,img[class*="avatar"]'));
    return /system|notice|status|tips?|remind|recall|withdraw/i.test(classes)
      || /聊天(?:中断|状态已恢复)|状态将在\d+天后消失|互聊\d+天|当天起互聊|已恢复.*去看看/.test(text)
      || (!hasAvatar && !/chat-item__content--(?:left|right)|chat-item__bubble--(?:me|other)/.test(classes));
  }

  function detectSenderLabel(messageNode, sender) {
    if (sender === 'system') return '系统消息';
    const avatars = safeQueryAll(messageNode, state.config.selectors.avatar);
    for (const avatar of avatars) {
      const label = cleanText(attrFirst(avatar, ['alt', 'title', 'aria-label']) || attrFirst(avatar.querySelector?.('img'), ['alt', 'title', 'aria-label']));
      if (label && !/^(?:我的)?头像$|^avatar$/i.test(label)) return label;
    }
    const quoteRoots = safeQueryAll(messageNode, state.config.selectors.quote);
    const labelled = [...messageNode.querySelectorAll('[class*="name"],[class*="nickname"],[data-nickname]')]
      .find((node) => !quoteRoots.some((quoteRoot) => quoteRoot === node || quoteRoot.contains(node)) && !node.closest('.xhs-im-bubble-card-note'));
    const label = cleanText(labelled?.getAttribute('data-nickname') || labelled?.innerText || '');
    if (label && !/^(?:我的)?头像$|^avatar$/i.test(label)) return label;
    if (sender === 'me') return state.participants.me || '我';
    if (sender === 'other') return state.participants.other || state.conversationTitle || '对方';
    return '未知';
  }

  function extractQuote(messageNode) {
    const candidates = safeQueryAll(messageNode, state.config.selectors.quote);
    const root = candidates.find((node) => cleanText(node.innerText || node.textContent));
    if (!root) return null;
    const senderEl = root.querySelector('.chat-item__ref-sender,[class*="name"],[class*="sender"],[data-nickname]');
    const sender = cleanText(senderEl?.getAttribute('data-nickname') || senderEl?.innerText || '').replace(/[：:]$/, '');
    const contentRoot = root.querySelector('.chat-item__ref-content') || root;
    const clone = contentRoot.cloneNode(true);
    clone.querySelectorAll('button,svg,[aria-hidden="true"]').forEach((node) => node.remove());
    const text = cleanText(clone.innerText || clone.textContent);
    const media = extractMedia(root);
    const cards = extractNoteCards(root);
    const videos = extractVideos(root);
    return text || media.images.length || media.emojis.length || cards.length || videos.length
      ? { sender, text, images: media.images, emojis: media.emojis, cards, videos }
      : null;
  }

  function extractMessageText(messageNode, quote) {
    const contentRoots = safeQueryAll(messageNode, state.config.selectors.content)
      .filter((node) => !safeQueryAll(messageNode, state.config.selectors.quote).some((quoteNode) => quoteNode.contains(node)));
    const root = contentRoots[0] || messageNode;
    const clone = root.cloneNode(true);
    const quoteSelector = selectorList(state.config.selectors.quote);
    if (quoteSelector) {
      try { clone.querySelectorAll(quoteSelector).forEach((node) => node.remove()); }
      catch (_) { /* invalid custom selector already reported elsewhere */ }
    }
    const avatarSelector = selectorList(state.config.selectors.avatar);
    if (avatarSelector) {
      try { clone.querySelectorAll(avatarSelector).forEach((node) => node.remove()); }
      catch (_) { /* ignore */ }
    }
    clone.querySelectorAll('button,svg,video,source,[aria-hidden="true"]').forEach((node) => node.remove());
    clone.querySelectorAll('.xhs-im-bubble-card-note,.xhs-im-bubble__card-comment').forEach((node) => node.remove());
    clone.querySelectorAll('img').forEach((img) => {
      const alt = cleanText(img.getAttribute('alt') || img.getAttribute('title') || '');
      const classes = String(img.className || '');
      const isInlineEmoji = /xhs-im-(?:inline|ref)-emoji|inline-emoji/i.test(classes);
      const marker = isInlineEmoji && alt ? `[表情:${alt.replace(/^\[|\]$/g, '')}]` : '';
      img.replaceWith(document.createTextNode(marker));
    });
    let text = cleanText(clone.innerText || clone.textContent);
    if (quote?.text && text.startsWith(quote.text)) text = cleanText(text.slice(quote.text.length));
    return text;
  }

  function parseTimeValue(raw) {
    const value = cleanText(raw);
    if (!value) return null;
    if (/^\d{10,13}$/.test(value)) {
      const number = Number(value);
      const date = new Date(value.length === 10 ? number * 1000 : number);
      if (!Number.isNaN(date.getTime())) return { label: date.toLocaleString('zh-CN'), raw: value };
    }
    if (looksLikeTime(value) || /\d{4}[-/.年]\d{1,2}/.test(value)) return { label: value, raw: value };
    return null;
  }

  function explicitMessageTime(messageNode) {
    const directNames = ['data-time', 'data-timestamp', 'data-create-time', 'data-created-at', 'datetime'];
    const direct = parseTimeValue(attrFirst(messageNode, directNames));
    if (direct) return { ...direct, source: 'message-attribute', inherited: false, exactForMessage: true };
    const nested = messageNode.querySelector('[datetime],[data-time],[data-timestamp],[class*="message-time"],[class*="messageTime"]');
    const nestedValue = parseTimeValue(attrFirst(nested, [...directNames, 'title']) || nested?.innerText || nested?.textContent);
    if (nestedValue) return { ...nestedValue, source: 'message-element', inherited: false, exactForMessage: true };
    return null;
  }

  function rawMessageId(messageNode) {
    return attrFirst(messageNode, [
      'data-message-id', 'data-msg-id', 'data-id', 'message-id', 'data-messageid'
    ]);
  }

  function parseMessage(messageNode, container, occurrenceMap) {
    let sender = detectSender(messageNode, container);
    if (isSystemMessage(messageNode, sender)) sender = 'system';
    const senderLabel = detectSenderLabel(messageNode, sender);
    const quote = extractQuote(messageNode);
    const media = extractMedia(messageNode);
    const videos = extractVideos(messageNode);
    const cards = extractNoteCards(messageNode);
    const text = extractMessageText(messageNode, quote);
    const realId = rawMessageId(messageNode);
    if (cards.length && realId) {
      const possibleNoteId = realId.split('.')[1];
      if (/^[a-f0-9]{24}$/i.test(possibleNoteId || '')) {
        for (const card of cards) {
          if (!card.href) {
            card.href = `https://www.xiaohongshu.com/explore/${possibleNoteId}`;
            card.hrefSource = 'message-id-derived';
          }
        }
      }
    }
    const signature = hashString(JSON.stringify({ sender, text, quote, cards, videos, images: media.images.map((item) => item.url), emojis: media.emojis.map((item) => item.url) }));
    const occurrence = (occurrenceMap.get(signature) || 0) + 1;
    occurrenceMap.set(signature, occurrence);
    const id = realId ? `msg:${realId}` : `synthetic:${signature}:${occurrence}`;
    return {
      id,
      messageId: realId || null,
      idSource: realId ? 'data-message-id' : 'content-fingerprint',
      sender,
      senderLabel,
      text,
      quote,
      cards,
      videos,
      images: media.images,
      emojis: media.emojis,
      explicitTime: explicitMessageTime(messageNode),
      inheritedTime: null,
      capturedAt: new Date().toISOString(),
      captureCount: 1
    };
  }

  function messageQuality(message) {
    return (message.text?.length || 0) + (message.images?.length || 0) * 20 + (message.emojis?.length || 0) * 8
      + (message.cards?.length || 0) * 40 + (message.videos?.length || 0) * 50 + (message.quote?.text?.length || 0) + (message.explicitTime ? 40 : 0) + (message.messageId ? 80 : 0);
  }

  function upsertMessage(message) {
    const existing = state.messages.get(message.id);
    if (!existing) {
      state.messages.set(message.id, message);
      if (message.messageId) state.seenRealIds += 1;
      registerMessageMedia(message);
      return true;
    }
    const preferred = messageQuality(message) > messageQuality(existing) ? message : existing;
    state.messages.set(message.id, {
      ...preferred,
      inheritedTime: preferred.inheritedTime || existing.inheritedTime || message.inheritedTime || null,
      captureCount: (existing.captureCount || 1) + 1,
      capturedAt: existing.capturedAt
    });
    registerMessageMedia(preferred);
    return false;
  }

  function registerMessageMedia(message) {
    const addVisual = (item) => {
      const url = item?.url;
      if (url && !url.startsWith('data:')) state.visualMediaUrls.add(url);
    };
    for (const item of [...(message.images || []), ...(message.emojis || [])]) addVisual(item);
    for (const item of [...(message.quote?.images || []), ...(message.quote?.emojis || [])]) addVisual(item);
    for (const card of [...(message.cards || []), ...(message.quote?.cards || [])]) {
      addVisual(card.cover);
      addVisual(card.authorAvatar);
    }
    for (const video of [...(message.videos || []), ...(message.quote?.videos || [])]) {
      if (video?.url && !video.url.startsWith('data:')) state.videoUrls.add(video.url);
      addVisual({ url: video?.posterUrl });
    }
  }

  function markerId(label, nextMessageId, previousMessageId) {
    return `time:${hashString(label)}:${nextMessageId || `after-${previousMessageId || 'unknown'}`}`;
  }

  function mergeTimeline(batch, direction = 'up') {
    const incoming = [...new Set(batch)].filter(Boolean);
    if (!incoming.length) return;
    state.timelineMergeCount += 1;
    if (!state.timeline.length) {
      state.timeline = incoming;
      return;
    }
    const incomingSet = new Set(incoming);
    const remainder = state.timeline.filter((id) => !incomingSet.has(id));
    state.timeline = direction === 'up' ? [...incoming, ...remainder] : [...remainder, ...incoming];
  }

  function yieldToPage() {
    return new Promise((resolve) => setTimeout(resolve, 0));
  }

  async function scanVisible(direction = 'up') {
    const container = state.container;
    if (!container?.isConnected) throw new Error('聊天滚动区域已离开页面，请重新打开会话后再开始。');
    const messageNodes = getMessageNodes(container);
    const timeNodes = getTimeSeparatorNodes(container, messageNodes);
    const newMessageNodes = messageNodes.filter((node) => !state.nodeMessageIds.has(node));
    const newTimeNodes = timeNodes.filter((node) => !state.nodeMarkerIds.has(node));
    if (!newMessageNodes.length && !newTimeNodes.length) {
      return { added: 0, parsed: 0, visible: messageNodes.length, timeSeparators: timeNodes.length, batch: [] };
    }
    const parsedByNode = new Map();
    const occurrenceMap = new Map();
    let added = 0;
    for (let nodeIndex = 0; nodeIndex < newMessageNodes.length; nodeIndex += 1) {
      const node = newMessageNodes[nodeIndex];
      try {
        const message = parseMessage(node, container, occurrenceMap);
        state.parsedNodeCount += 1;
        state.nodeMessageIds.set(node, message.id);
        if (upsertMessage(message)) added += 1;
        parsedByNode.set(node, message);
      } catch (error) { recordError('解析一条消息失败', error); }
      if ((nodeIndex + 1) % state.config.parseChunkSize === 0) {
        await yieldToPage();
        if (state.stopRequested) break;
      }
    }
    const orderedNodes = sortDomOrder([...newMessageNodes, ...newTimeNodes]);
    const rawEvents = [];
    for (const node of orderedNodes) {
      if (parsedByNode.has(node)) rawEvents.push({ type: 'message', node, message: parsedByNode.get(node) });
      else rawEvents.push({ type: 'time', node, label: cleanText(node.innerText || node.textContent) });
    }
    const batch = [];
    const nextMessageIds = new Array(rawEvents.length).fill('');
    let nextMessageId = '';
    for (let index = rawEvents.length - 1; index >= 0; index -= 1) {
      nextMessageIds[index] = nextMessageId;
      if (rawEvents[index].type === 'message') nextMessageId = rawEvents[index].message.id;
    }
    let activeMarker = null;
    let previousMessageId = '';
    for (let index = 0; index < rawEvents.length; index += 1) {
      const event = rawEvents[index];
      if (event.type === 'time') {
        const next = nextMessageIds[index];
        const previous = previousMessageId;
        let id = markerId(event.label, next, previous);
        if (state.markers.has(id)) id = `${id}:${++state.markerSerial}`;
        activeMarker = { id, label: event.label, nextMessageId: next || null, previousMessageId: previous || null };
        state.markers.set(id, activeMarker);
        state.nodeMarkerIds.set(event.node, id);
        batch.push(id);
      } else {
        previousMessageId = event.message.id;
        batch.push(event.message.id);
        if (!event.message.explicitTime && activeMarker) {
          const stored = state.messages.get(event.message.id);
          if (stored && !stored.inheritedTime) {
            stored.inheritedTime = {
              label: activeMarker.label,
              source: 'time-separator',
              markerId: activeMarker.id,
              inherited: true,
              exactForMessage: false
            };
          }
        }
      }
    }
    mergeTimeline(batch, direction);
    return { added, parsed: newMessageNodes.length, visible: messageNodes.length, timeSeparators: timeNodes.length, batch };
  }

  function setCollectStatus(label, extra = '', force = false) {
    const now = Date.now();
    if (!force && now - state.lastCollectStatusAt < state.config.statusUpdateMs) return;
    state.lastCollectStatusAt = now;
    const base = `消息 ${state.messages.size} · 图片/表情 ${state.visualMediaUrls.size} · 视频 ${state.videoUrls.size} · 时间分隔 ${state.markers.size}`;
    setStatus(label, extra ? `${base} · ${extra}` : base);
  }

  function applyTimelineTimes() {
    let active = null;
    for (const id of state.timeline) {
      if (state.markers.has(id)) {
        active = state.markers.get(id);
        continue;
      }
      const message = state.messages.get(id);
      if (message && !message.explicitTime && active) {
        message.inheritedTime = {
          label: active.label,
          source: 'time-separator',
          markerId: active.id,
          inherited: true,
          exactForMessage: false
        };
      }
    }
  }

  function wait(ms) {
    return new Promise((resolve) => setTimeout(resolve, ms));
  }

  async function waitForMutation(container, timeoutMs) {
    return new Promise((resolve) => {
      let done = false;
      const finish = (changed) => {
        if (done) return;
        done = true;
        observer.disconnect();
        clearTimeout(timer);
        resolve(changed);
      };
      const observer = new MutationObserver(() => finish(true));
      observer.observe(container, { childList: true, subtree: true, attributes: true, attributeFilter: ['src', 'class', 'style'] });
      const timer = setTimeout(() => finish(false), timeoutMs);
    });
  }

  function dispatchScroll(container) {
    try {
      container.dispatchEvent(new Event('scroll', { bubbles: true }));
      container.dispatchEvent(new WheelEvent('wheel', { deltaY: -900, bubbles: true, cancelable: true }));
    } catch (_) { /* browser may reject synthetic wheel options */ }
  }

  async function moveToNewest(container) {
    setStatus('先定位到当前会话底部…');
    for (let attempt = 0; attempt < 2 && !state.stopRequested; attempt += 1) {
      container.scrollTop = container.scrollHeight;
      dispatchScroll(container);
      await wait(120);
    }
    await scanVisible('down');
  }

  async function collectAll(options = {}) {
    if (state.running) return api;
    state.config = mergeConfig(DEFAULTS, options);
    resetCollection();
    state.container = findScrollContainer();
    if (!state.container) {
      const info = diagnose();
      setStatus('未找到私信滚动区', '请确认已打开具体会话；详见控制台诊断。', true);
      console.error(`[${GLOBAL_NAME}] 未找到滚动区`, info);
      throw new Error('未找到包含私信消息的滚动区域。');
    }
    state.running = true;
    state.operation = 'collect';
    state.stopRequested = false;
    state.startedAt = new Date().toISOString();
    state.conversationTitle = detectConversationTitle();
    state.participants = detectParticipantNames(state.container, state.conversationTitle);
    updateButtons();

    try {
      if (state.container.scrollTop <= 3) {
        setStatus('检测到已在顶部', '直接分批解析现有消息，不再先跳回底部');
        await scanVisible('up');
      } else {
        await moveToNewest(state.container);
      }
      let lastScrollHeight = -1;
      let lastOldest = '';
      let lastNewAt = Date.now();
      for (let round = 1; round <= state.config.maxRounds && !state.stopRequested; round += 1) {
        state.rounds = round;
        const beforeCount = state.messages.size;
        const beforeHeight = state.container.scrollHeight;
        const beforeTop = state.container.scrollTop;
        const firstMessage = state.timeline.find((id) => state.messages.has(id)) || '';
        setCollectStatus(`采集中：第 ${round} 轮`, '等待更早消息');

        const mutationPromise = waitForMutation(state.container, state.config.mutationWaitMs);
        const distance = Math.max(1000, state.container.clientHeight * state.config.scrollRatio);
        if (state.config.fastJumpToTop) state.container.scrollTop = 0;
        else if (beforeTop > 2) state.container.scrollTop = Math.max(0, beforeTop - distance);
        else state.container.scrollTop = 0;
        dispatchScroll(state.container);
        await wait(state.config.settleMs);
        await mutationPromise;
        await wait(20);

        let afterResult = { added: 0 };
        try { afterResult = await scanVisible('up'); }
        catch (error) { recordError('滚动后扫描失败', error); }
        setCollectStatus(`采集中：第 ${round} 轮`, afterResult.parsed ? `本轮新节点 ${afterResult.parsed} 条` : '暂时没有新增');
        const afterHeight = state.container.scrollHeight;
        const afterTop = state.container.scrollTop;
        const totalAdded = state.messages.size - beforeCount;
        const atTop = afterTop <= 3;
        const unchanged = totalAdded === 0 && afterResult.added === 0
          && Math.abs(afterHeight - lastScrollHeight) < 3 && firstMessage === lastOldest;
        state.stableRounds = atTop && unchanged ? state.stableRounds + 1 : 0;
        if (totalAdded > 0 || afterResult.added > 0) lastNewAt = Date.now();
        lastScrollHeight = afterHeight;
        lastOldest = firstMessage;

        if (atTop && unchanged) {
          const idleMs = Date.now() - lastNewAt;
          const remaining = Math.max(0, state.config.historyIdleMs - idleMs);
          setCollectStatus(`已到顶部：第 ${round} 轮`, remaining
            ? `等待可能较慢的网络加载：还会观察约 ${Math.ceil(remaining / 1000)} 秒；确认完整可点“停止”`
            : '网络宽限期结束，准备完成');
          if (idleMs >= state.config.historyIdleMs) break;
        }
        if (atTop && beforeHeight === afterHeight && totalAdded === 0) await wait(250);
      }
      applyTimelineTimes();
      state.finishedAt = new Date().toISOString();
      const stopped = state.stopRequested;
      setStatus(
        stopped ? `已停止：保留 ${state.messages.size} 条` : `采集完成：${state.messages.size} 条`,
        `${state.markers.size} 个时间分隔；真实消息 ID ${state.seenRealIds} 条；现在可以导出`
      );
    } catch (error) {
      recordError('采集被异常中断', error);
      setStatus(`采集异常：已保留 ${state.messages.size} 条`, error.message || String(error), true);
      throw error;
    } finally {
      state.running = false;
      state.operation = null;
      updateButtons();
    }
    return api;
  }

  function stop() {
    state.stopRequested = true;
    const detail = state.operation === 'collect'
      ? `已保留 ${state.messages.size} 条；当前等待结束后即可导出`
      : '正在结束图片任务；已成功处理的部分会保留';
    setStatus('正在停止…', detail);
    updateButtons();
  }

  function resetCollection() {
    state.stopRequested = false;
    state.messages.clear();
    state.timeline = [];
    state.markers.clear();
    state.seenRealIds = 0;
    state.rounds = 0;
    state.stableRounds = 0;
    state.errors = [];
    state.nodeMessageIds = new WeakMap();
    state.nodeMarkerIds = new WeakMap();
    state.markerSerial = 0;
    state.parsedNodeCount = 0;
    state.timelineMergeCount = 0;
    state.visualMediaUrls.clear();
    state.videoUrls.clear();
    state.lastCollectStatusAt = 0;
    state.startedAt = null;
    state.finishedAt = null;
  }

  function detectConversationTitle() {
    const candidates = [
      '.xhs-im-chat-window__header-name',
      '.xhs-im-chat-window__header-avatar[alt]',
      '[class*="chat"] [class*="title"]', '[class*="conversation"] [class*="title"]',
      '[class*="header"] [class*="name"]', 'main h1', 'main h2'
    ];
    for (const selector of candidates) {
      const node = document.querySelector(selector);
      const text = cleanText(node?.innerText || node?.getAttribute?.('alt'));
      if (text && text.length <= 80) return text;
    }
    return cleanText(document.title).replace(/\s*[-|_].*小红书.*$/i, '') || '小红书私信';
  }

  function usableNickname(value) {
    const label = cleanText(value);
    if (!label || label.length > 80) return '';
    if (/^(?:我的)?头像$|^avatar$|^对方$|^未知$/i.test(label)) return '';
    return label;
  }

  function detectParticipantNames(container, conversationTitle) {
    const names = {
      me: usableNickname(state.config.myName) || '我',
      other: usableNickname(state.config.otherName) || usableNickname(conversationTitle) || '对方'
    };
    try {
      if (!state.config.myName) {
        const selfSelectors = [
          'header [class*="user-info"] [class*="name"]',
          'header [class*="user"] [class*="nickname"]',
          '[class*="account-info"] [class*="name"]',
          '[class*="profile"] [class*="nickname"]'
        ];
        for (const selector of selfSelectors) {
          const candidate = [...document.querySelectorAll(selector)]
            .find((node) => !container.contains(node) && isElementVisible(node));
          const label = usableNickname(candidate?.innerText || candidate?.textContent);
          if (label && label !== names.other) { names.me = label; break; }
        }
      }
      for (const messageNode of getMessageNodes(container)) {
        const sender = detectSender(messageNode, container);
        const avatars = safeQueryAll(messageNode, state.config.selectors.avatar);
        for (const avatar of avatars) {
          const img = avatar.matches?.('img') ? avatar : avatar.querySelector?.('img');
          const label = usableNickname(attrFirst(avatar, ['alt', 'title', 'aria-label']) || attrFirst(img, ['alt', 'title', 'aria-label']));
          if (!label) continue;
          if (sender === 'me') names.me = label;
          if (sender === 'other') names.other = label;
        }
      }
    } catch (error) { recordError('读取会话昵称失败', error); }
    return names;
  }

  function orderedMessages() {
    applyTimelineTimes();
    const ordered = [];
    const seen = new Set();
    for (const id of state.timeline) {
      const message = state.messages.get(id);
      if (message && !seen.has(id)) {
        ordered.push(message);
        seen.add(id);
      }
    }
    for (const [id, message] of state.messages) {
      if (!seen.has(id)) ordered.push(message);
    }
    return ordered;
  }

  function resolvedTime(message) {
    if (message.explicitTime) return message.explicitTime;
    if (message.inheritedTime) return message.inheritedTime;
    return { label: null, source: 'unknown', inherited: false, exactForMessage: false };
  }

  function localDateKey(date) {
    const pad = (value) => String(value).padStart(2, '0');
    return `${date.getFullYear()}-${pad(date.getMonth() + 1)}-${pad(date.getDate())}`;
  }

  function formatResolvedDate(date) {
    const pad = (value) => String(value).padStart(2, '0');
    return `${date.getFullYear()}-${pad(date.getMonth() + 1)}-${pad(date.getDate())} ${pad(date.getHours())}:${pad(date.getMinutes())}`;
  }

  function resolvePageTimeLabel(label, cursor, exportedAt) {
    const value = cleanText(label);
    if (!value) return null;
    const exported = new Date(exportedAt);
    const base = new Date(exported.getFullYear(), exported.getMonth(), exported.getDate());
    const clockMatch = value.match(/(\d{1,2}):(\d{2})(?::\d{2})?/);
    const hours = clockMatch ? Number(clockMatch[1]) : 0;
    const minutes = clockMatch ? Number(clockMatch[2]) : 0;
    let date = null;
    let match = value.match(/(\d{4})[年./-](\d{1,2})[月./-](\d{1,2})/);
    if (match) {
      date = new Date(Number(match[1]), Number(match[2]) - 1, Number(match[3]));
    } else if ((match = value.match(/(\d{1,2})月(\d{1,2})日/))) {
      date = new Date(base.getFullYear(), Number(match[1]) - 1, Number(match[2]));
      if (date.getTime() > base.getTime() + 86400000) date.setFullYear(date.getFullYear() - 1);
    } else if (/前天/.test(value)) {
      date = new Date(base); date.setDate(date.getDate() - 2);
    } else if (/昨天/.test(value)) {
      date = new Date(base); date.setDate(date.getDate() - 1);
    } else if (/今天/.test(value)) {
      date = new Date(base);
    } else if ((match = value.match(/(?:星期|周)([一二三四五六日天])/))) {
      const target = { 日: 0, 天: 0, 一: 1, 二: 2, 三: 3, 四: 4, 五: 5, 六: 6 }[match[1]];
      const difference = (base.getDay() - target + 7) % 7;
      date = new Date(base); date.setDate(date.getDate() - difference);
    } else if (clockMatch) {
      date = cursor ? new Date(cursor) : new Date(base);
      const previousMinutes = cursor ? cursor.getHours() * 60 + cursor.getMinutes() : -1;
      const currentMinutes = hours * 60 + minutes;
      if (cursor && currentMinutes < previousMinutes && localDateKey(date) < localDateKey(base)) date.setDate(date.getDate() + 1);
    }
    if (!date || Number.isNaN(date.getTime())) return null;
    date.setHours(hours, minutes, 0, 0);
    return date;
  }

  function attachResolvedTimes(messages, exportedAt) {
    let cursor = null;
    let activeLabel = null;
    let activeResolved = null;
    let first = null;
    let last = null;
    for (const message of messages) {
      const time = message.time || {};
      if (time.label && time.label !== activeLabel) {
        activeLabel = time.label;
        activeResolved = resolvePageTimeLabel(time.label, cursor, exportedAt);
        if (activeResolved) cursor = activeResolved;
      }
      const resolved = time.exactForMessage
        ? resolvePageTimeLabel(time.label, cursor, exportedAt) || activeResolved
        : activeResolved;
      if (resolved) {
        message.time.resolvedLocal = formatResolvedDate(resolved);
        message.time.dateKey = localDateKey(resolved);
        if (!first) first = new Date(resolved);
        last = new Date(resolved);
      }
    }
    return {
      start: first ? formatResolvedDate(first) : null,
      end: last ? formatResolvedDate(last) : null,
      display: first && last ? `${formatResolvedDate(first)} ～ ${formatResolvedDate(last)}` : '页面未提供可解析的时间范围',
      note: '由页面时间分隔解析；分隔时间不是每条消息的独立精确时间。'
    };
  }

  function exportData() {
    const exportedAt = new Date().toISOString();
    const messages = orderedMessages().map((message, index) => ({
      order: index + 1,
      messageId: message.messageId,
      idSource: message.idSource,
      sender: message.sender,
      senderLabel: message.senderLabel,
      time: { ...resolvedTime(message) },
      text: message.text,
      quote: message.quote,
      cards: message.cards || [],
      videos: message.videos || [],
      emojis: message.emojis,
      images: message.images,
      capturedAt: message.capturedAt
    }));
    const timeRange = attachResolvedTimes(messages, exportedAt);
    return {
      schemaVersion: 1,
      exporter: `${GLOBAL_NAME} ${VERSION}`,
      pageUrl: location.href,
      conversationTitle: state.conversationTitle || detectConversationTitle(),
      participants: { ...state.participants },
      exportedAt,
      timeRange,
      collection: {
        startedAt: state.startedAt,
        finishedAt: state.finishedAt,
        stoppedManually: state.stopRequested,
        rounds: state.rounds,
        messageCount: messages.length,
        realMessageIdCount: state.seenRealIds,
        timeSeparatorCount: state.markers.size,
        errors: state.errors
      },
      timeSemantics: {
        messageAttribute: '页面把时间直接放在该消息的属性或子元素上，可归属于该条消息。',
        timeSeparator: '页面只显示分组时间；后续消息继承该分隔文字，不代表每条消息都在同一分钟发送。',
        unknown: '当前已加载 DOM 中没有可关联的时间。'
      },
      messages
    };
  }

  function safeFilename(value) {
    return cleanText(value || '小红书私信')
      .replace(/[\\/:*?"<>|]/g, '_')
      .replace(/\.+$/g, '')
      .slice(0, 80) || '小红书私信';
  }

  function timestampForFilename() {
    const date = new Date();
    const pad = (number) => String(number).padStart(2, '0');
    return `${date.getFullYear()}${pad(date.getMonth() + 1)}${pad(date.getDate())}_${pad(date.getHours())}${pad(date.getMinutes())}${pad(date.getSeconds())}`;
  }

  function archiveBaseName(data) {
    const nickname = data.participants?.other || data.conversationTitle || '对方';
    return `${safeFilename(nickname)}的私信记录`;
  }

  function downloadBlob(blob, filename) {
    const url = URL.createObjectURL(blob);
    const link = document.createElement('a');
    link.href = url;
    link.download = filename;
    link.style.display = 'none';
    document.body.appendChild(link);
    link.click();
    link.remove();
    setTimeout(() => URL.revokeObjectURL(url), 30000);
  }

  function toTxt(data) {
    const lines = [
      `${data.participants?.other || data.conversationTitle}的私信记录`,
      `导出时间：${new Date(data.exportedAt).toLocaleString('zh-CN')}`,
      `私信时间范围：${data.timeRange?.display || '未知'}`,
      `页面：${data.pageUrl}`,
      `消息数：${data.messages.length}`,
      '',
      '说明：标注“分隔时间（继承）”的时间只表示该消息位于该时间分组之后，不是这条消息独立、精确的发送时间。',
      ''
    ];
    let previousSeparator = Symbol('none');
    for (const message of data.messages) {
      const time = message.time || {};
      if (time.source === 'time-separator' && time.label !== previousSeparator) {
        lines.push(`──────── ${time.label}（页面时间分隔）────────`);
        previousSeparator = time.label;
      }
      const timeLabel = time.source === 'message-attribute' || time.source === 'message-element'
        ? ` [${time.label}，逐条时间]`
        : time.source === 'unknown' ? ' [时间未知]' : '';
      lines.push(`${message.senderLabel || senderText(message.sender)}${timeLabel}：`);
      if (message.quote) {
        const quoteSender = message.quote.sender ? `${message.quote.sender}：` : '';
        lines.push(`  ↪ 引用 ${quoteSender}${message.quote.text || '[媒体]'}`);
      }
      let messageText = message.text || '';
      if (!messageText && (message.emojis || []).length) {
        messageText = message.emojis.map((emoji) => `[表情:${emoji.alt || '表情'}]`).join('');
      }
      if (messageText) lines.push(messageText);
      for (const card of message.cards || []) {
        if (card.type === 'comment') {
          lines.push(`[${card.label || '分享评论'}] ${card.text || ''}`);
          if (card.title) lines.push(`${card.from || '来自笔记'}：${card.title}`);
        } else {
          lines.push(`[分享笔记${card.isVideo ? '·视频' : ''}] ${card.title || '无标题'}`);
          if (card.author) lines.push(`作者：${card.author}`);
        }
        if (card.href) lines.push(`笔记链接：${card.href}`);
        if (card.cover?.url) lines.push(`封面：${card.cover.url}`);
      }
      for (const video of message.videos || []) lines.push(`[视频] ${video.url || video.posterUrl}`);
      for (const image of message.images || []) lines.push(`[图片原始/最佳 URL] ${image.url}`);
      if (!messageText && !message.quote && !(message.cards || []).length && !(message.images || []).length && !(message.videos || []).length) lines.push('[未识别内容]');
      lines.push('');
    }
    return lines.join('\n');
  }

  function senderText(sender) {
    return sender === 'me' ? '我' : sender === 'other' ? '对方' : sender === 'system' ? '系统消息' : '未知发送方';
  }

  function escapeHtml(value) {
    return String(value ?? '').replace(/[&<>"']/g, (char) => ({
      '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;'
    }[char]));
  }

  function htmlText(value) {
    return escapeHtml(value).replace(/\n/g, '<br>');
  }

  function assetSrc(item, imageMap) {
    return imageMap.get(item?.url) || item?.thumbnailUrl || item?.url || '';
  }

  function renderRichText(text, emojis, imageMap) {
    const value = String(text || '');
    const pool = [...(emojis || [])];
    let result = '';
    let cursor = 0;
    const marker = /\[表情:([^\]]+)\]/g;
    let match;
    while ((match = marker.exec(value))) {
      result += htmlText(value.slice(cursor, match.index));
      const wanted = cleanText(match[1]);
      let index = pool.findIndex((item) => cleanText(item.alt) === wanted);
      if (index < 0) index = pool.length ? 0 : -1;
      const emoji = index >= 0 ? pool.splice(index, 1)[0] : null;
      result += emoji
        ? `<img class="emoji" src="${escapeHtml(assetSrc(emoji, imageMap))}" alt="${escapeHtml(emoji.alt || wanted || '表情')}" title="${escapeHtml(emoji.alt || wanted || '表情')}">`
        : `<span class="emoji-text">${escapeHtml(match[0])}</span>`;
      cursor = marker.lastIndex;
    }
    result += htmlText(value.slice(cursor));
    for (const emoji of pool) {
      result += `<img class="emoji" src="${escapeHtml(assetSrc(emoji, imageMap))}" alt="${escapeHtml(emoji.alt || '表情')}" title="${escapeHtml(emoji.alt || '表情')}">`;
    }
    return result;
  }

  function renderNoteCard(card, imageMap) {
    if (card.type === 'comment') return renderCommentCard(card, imageMap);
    const coverSrc = assetSrc(card.cover, imageMap);
    const avatarSrc = assetSrc(card.authorAvatar, imageMap);
    const tag = card.href ? 'a' : 'div';
    const linkAttrs = card.href ? ` href="${escapeHtml(card.href)}" target="_blank" rel="noreferrer"` : '';
    return `<${tag} class="note-card"${linkAttrs}>${coverSrc ? `<div class="note-cover-wrap"><img class="note-cover" src="${escapeHtml(coverSrc)}" alt="笔记封面" loading="lazy">${card.isVideo ? '<span class="video-badge">▶ 视频</span>' : ''}</div>` : ''}<div class="note-info"><strong>${escapeHtml(card.title || '分享的笔记')}</strong><div class="note-author">${avatarSrc ? `<img src="${escapeHtml(avatarSrc)}" alt="">` : ''}<span>${escapeHtml(card.author || '未知作者')}</span></div></div></${tag}>`;
  }

  function renderCommentCard(card, imageMap) {
    const coverSrc = assetSrc(card.cover, imageMap);
    const tag = card.href ? 'a' : 'div';
    const linkAttrs = card.href ? ` href="${escapeHtml(card.href)}" target="_blank" rel="noreferrer"` : '';
    return `<${tag} class="comment-card"${linkAttrs}><div class="comment-label">${escapeHtml(card.label || '分享评论')}</div><div class="comment-text">${htmlText(card.text || '[图片]')}</div>${card.title || coverSrc ? `<div class="comment-note">${coverSrc ? `<img src="${escapeHtml(coverSrc)}" alt="笔记封面" loading="lazy">` : ''}<div><span>${escapeHtml(card.from || '来自笔记')}</span><strong>${escapeHtml(card.title || '笔记')}</strong></div></div>` : ''}</${tag}>`;
  }

  function renderPhotos(images, imageMap, className = 'photo') {
    return (images || []).map((item) => {
      const src = assetSrc(item, imageMap);
      return `<figure><a href="${escapeHtml(src || item.url)}" target="_blank" rel="noreferrer"><img class="${className}" src="${escapeHtml(src)}" alt="${escapeHtml(item.alt || '私信图片')}" loading="lazy"></a></figure>`;
    }).join('');
  }

  function renderVideos(videos, imageMap) {
    return (videos || []).map((item) => {
      const src = imageMap.get(item.url) || item.url || '';
      const poster = imageMap.get(item.posterUrl) || item.posterUrl || '';
      if (!src) return poster ? `<img class="photo video-poster" src="${escapeHtml(poster)}" alt="视频封面">` : '';
      return `<video class="video-message" controls preload="metadata"${poster ? ` poster="${escapeHtml(poster)}"` : ''}><source src="${escapeHtml(src)}"${item.mimeType ? ` type="${escapeHtml(item.mimeType)}"` : ''}>浏览器无法播放此视频，<a href="${escapeHtml(src)}">点击打开视频文件</a>。</video>`;
    }).join('');
  }

  function renderQuote(quote, imageMap) {
    if (!quote) return '';
    const text = renderRichText(quote.text || '', quote.emojis || [], imageMap);
    const cards = (quote.cards || []).map((card) => renderNoteCard(card, imageMap)).join('');
    const photos = renderPhotos(quote.images || [], imageMap, 'quote-photo');
    const videos = renderVideos(quote.videos || [], imageMap);
    return `<div class="quote-preview">${quote.sender ? `<b>${escapeHtml(quote.sender)}</b>` : ''}${text ? `<span>${text}</span>` : ''}${cards}${photos}${videos}</div>`;
  }

  function buildHtml(data, imageMap = new Map()) {
    let activeSeparator = Symbol('none');
    const timeAnchors = [];
    const body = data.messages.map((message, messageIndex) => {
      const time = message.time || {};
      let separator = '';
      if (time.source === 'time-separator' && time.label !== activeSeparator) {
        activeSeparator = time.label;
        const anchor = `time-${timeAnchors.length + 1}`;
        timeAnchors.push({ anchor, label: time.label, dateKey: time.dateKey || '' });
        separator = `<div class="time-separator" id="${anchor}" data-date="${escapeHtml(time.dateKey || '')}"><span>${escapeHtml(time.label)}</span></div>`;
      }
      const side = message.sender === 'me' ? 'me' : message.sender === 'other' ? 'other' : message.sender === 'system' ? 'system' : 'unknown';
      const preciseTime = time.exactForMessage && time.label
        ? `<time title="页面为该条消息提供的时间">${escapeHtml(time.label)}</time>`
        : time.source === 'unknown' ? '<time class="uncertain">时间未知</time>' : '';
      const content = (message.text || (message.emojis || []).length)
        ? `<div class="text">${renderRichText(message.text || '', message.emojis || [], imageMap)}</div>` : '';
      const cards = (message.cards || []).map((card) => renderNoteCard(card, imageMap)).join('');
      const imageHtml = renderPhotos(message.images || [], imageMap);
      const videoHtml = renderVideos(message.videos || [], imageMap);
      const quote = renderQuote(message.quote, imageMap);
      const searchable = [message.senderLabel, time.label, message.text, message.quote?.text,
        ...(message.cards || []).flatMap((card) => [card.label, card.text, card.title, card.author])].filter(Boolean).join(' ').toLowerCase();
      const commentClass = (message.cards || []).some((card) => card.type === 'comment') ? ' has-comment-card' : '';
      return `${separator}<article class="message ${side}${commentClass}" data-order="${messageIndex + 1}" data-date="${escapeHtml(time.dateKey || '')}" data-search="${escapeHtml(searchable)}"><div class="meta"><b>${escapeHtml(message.senderLabel || senderText(message.sender))}</b>${preciseTime}</div><div class="bubble">${quote}${content}${cards}${imageHtml}${videoHtml}</div></article>`;
    }).join('\n');

    const dates = [...new Set(timeAnchors.map((item) => item.dateKey).filter(Boolean))];
    const minDate = dates[0] || '';
    const maxDate = dates[dates.length - 1] || '';
    const title = `${data.participants?.other || data.conversationTitle}的私信记录`;

    return `<!doctype html>
<html lang="zh-CN"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>${escapeHtml(title)}</title>
<style>
:root{color-scheme:light;--bg:#f5f6f8;--mine:#ff2442;--other:#fff;--ink:#202124;--muted:#747982;--accent:#5b4cf0}*{box-sizing:border-box}html{scroll-behavior:smooth}body{margin:0;background:var(--bg);color:var(--ink);font:15px/1.58 system-ui,-apple-system,"Segoe UI","PingFang SC","Microsoft YaHei",sans-serif}.page{max-width:960px;margin:auto;padding:24px 18px 64px}.header{background:#fff;border-radius:18px;padding:22px;box-shadow:0 3px 18px #0000000b;margin-bottom:14px}.header h1{font-size:24px;margin:0 0 10px}.header p{margin:4px 0;color:var(--muted);word-break:break-all}.notice{background:#fff8df;border:1px solid #f0d783;border-radius:11px;padding:10px 12px;margin-top:13px;color:#6e5913}.tools{position:sticky;top:8px;z-index:10;background:#fffffff2;backdrop-filter:blur(12px);padding:12px;border:1px solid #e2e4e8;border-radius:15px;box-shadow:0 6px 24px #00000012;margin-bottom:20px}.search-row,.date-row{display:flex;align-items:center;gap:8px}.date-row{margin-top:9px;padding-top:9px;border-top:1px solid #eceef1}.search-box{position:relative;flex:1}.search-box input{width:100%;padding:10px 42px 10px 38px}.search-icon{position:absolute;left:13px;top:50%;transform:translateY(-50%);color:#8a8f98}.icon-button,.tools input,.tools button{border:1px solid #cfd3da;border-radius:10px;background:#fff;font:inherit}.tools button{padding:9px 12px;cursor:pointer}.tools button:hover{background:#f1f2f5}.tools button:disabled{opacity:.45;cursor:default}.clear-search{position:absolute;right:6px;top:50%;transform:translateY(-50%);border:0!important;padding:4px 9px!important;color:#777}.result-count{min-width:94px;text-align:center;color:var(--muted);font-size:12px}.date-label{font-weight:650;white-space:nowrap}.date-row input{padding:8px 10px;min-width:165px}.date-status{color:var(--muted);font-size:12px;overflow:hidden;text-overflow:ellipsis;white-space:nowrap}.time-separator{text-align:center;margin:28px 0 15px;scroll-margin-top:150px}.time-separator span{display:inline-block;padding:4px 10px;border-radius:20px;background:#e6e8ec;color:#626772;font-size:12px}.message{display:flex;flex-direction:column;margin:13px 0;max-width:78%;scroll-margin-top:150px;transition:filter .15s,outline-color .15s}.message.me{margin-left:auto;align-items:flex-end}.message.other{margin-right:auto;align-items:flex-start}.message.unknown{margin-left:auto;margin-right:auto}.message.system{max-width:100%;margin:16px auto;align-items:center}.message.system .meta{display:none}.message.system .bubble{width:min(100%,900px);text-align:center;background:#fff;color:#444;border-radius:14px}.message.search-match{filter:drop-shadow(0 0 4px #ffcf36)}.message.active-match{outline:3px solid #ffbf00;outline-offset:5px;border-radius:15px}.meta{display:flex;gap:8px;align-items:center;margin:0 6px 4px;color:var(--muted);font-size:12px;flex-wrap:wrap}.meta b{color:#444}.bubble{max-width:100%;background:var(--other);border-radius:16px;padding:11px 14px;box-shadow:0 1px 8px #0000000a;overflow-wrap:anywhere}.me .bubble{background:var(--mine);color:#fff}.text{white-space:normal}.quote-preview{margin:0 0 9px;padding:9px 11px;border-left:3px solid #7668ff;background:#f0efff;color:#39405a;border-radius:11px;display:flex;gap:3px;flex-direction:column;overflow-wrap:anywhere}.quote-preview b{color:#222b4a}.me .quote-preview{background:#fff;color:#39405a}.text+.note-card,.quote-preview+.text{margin-top:6px}.emoji{width:1.25em;height:1.25em;object-fit:contain;vertical-align:-.22em;margin:0 .08em}.emoji-text{white-space:nowrap}.photo{display:block;max-width:min(100%,540px);max-height:720px;object-fit:contain;border-radius:10px;margin-top:8px;background:#eee}figure{margin:0}.quote-photo{max-width:220px;max-height:180px;border-radius:7px}.note-card{display:block;width:min(100%,320px);margin:0;text-decoration:none;color:#202124;background:#f1f1f2;border-radius:14px;overflow:hidden}.me .note-card{background:#f5f5f5;color:#202124}.note-cover-wrap{position:relative}.note-cover{display:block;width:100%;max-height:360px;object-fit:cover;background:#ddd}.video-badge{position:absolute;right:9px;top:9px;padding:3px 7px;border-radius:12px;background:#0009;color:#fff;font-size:11px}.note-info{padding:10px 12px}.note-info strong{display:block;font-size:15px;line-height:1.4}.note-author{display:flex;align-items:center;gap:6px;margin-top:8px;color:#777}.note-author img{width:24px;height:24px;border-radius:50%;object-fit:cover}.message.has-comment-card .bubble{padding:0;background:transparent;box-shadow:none}.comment-card{display:block;width:min(100%,340px);padding:12px;text-decoration:none;color:#222;background:#f1f1f2;border-radius:15px}.comment-label{font-size:12px;color:#81858d;margin-bottom:4px}.comment-text{font-size:15px;line-height:1.45}.comment-note{display:flex;gap:9px;align-items:center;margin-top:10px;padding-top:10px;border-top:1px solid #d7d9dd}.comment-note img{width:48px;height:48px;border-radius:5px;object-fit:cover}.comment-note div{display:flex;min-width:0;flex-direction:column}.comment-note span{font-size:11px;color:#81858d}.comment-note strong{font-size:13px;white-space:nowrap;overflow:hidden;text-overflow:ellipsis}.video-message{display:block;width:min(100%,540px);max-height:720px;margin-top:8px;border-radius:10px;background:#111}.video-poster{position:relative}time.uncertain{font-style:italic}@media(max-width:680px){.page{padding:12px 9px 40px}.message{max-width:91%}.header{padding:15px}.search-row,.date-row{flex-wrap:wrap}.result-count{order:4;width:100%;text-align:left}}
</style></head><body><main class="page"><section class="header"><h1>${escapeHtml(title)}</h1><p>导出时间：${escapeHtml(new Date(data.exportedAt).toLocaleString('zh-CN'))}</p><p>私信时间范围：${escapeHtml(data.timeRange?.display || '未知')}</p><p>消息数：${data.messages.length}　参与者：${escapeHtml(data.participants?.me || '我')} / ${escapeHtml(data.participants?.other || data.conversationTitle)}</p><div class="notice">页面时间分隔不等于每条消息的精确发送时间。${imageMap.size ? ` 已将 ${imageMap.size} 个图片/表情资源保存到离线包。` : ' 当前是快速 HTML，图片仍引用网络地址。'}</div></section><section class="tools"><div class="search-row"><div class="search-box"><span class="search-icon">⌕</span><input id="searchInput" type="search" placeholder="搜索正文、引用、昵称或笔记…"><button id="clearSearch" class="clear-search" type="button" title="清除">×</button></div><span class="result-count" id="resultCount">输入关键词检索</span><button id="prevResult" class="icon-button" type="button" title="上一条">↑</button><button id="nextResult" class="icon-button" type="button" title="下一条">↓</button></div><div class="date-row"><span class="date-label">按日期跳转</span><input id="calendarJump" type="date" min="${escapeHtml(minDate)}" max="${escapeHtml(maxDate)}"><button id="prevDate" type="button">前一日</button><button id="jumpDate" class="primary" type="button">跳转</button><button id="nextDate" type="button">后一日</button><span id="dateStatus" class="date-status">${dates.length ? `可选 ${dates.length} 个有记录的日期` : '页面时间无法解析为日期'}</span></div></section><section id="messages">${body}</section></main><script>(()=>{const q=document.getElementById('searchInput'),count=document.getElementById('resultCount'),items=[...document.querySelectorAll('.message')],prev=document.getElementById('prevResult'),next=document.getElementById('nextResult'),calendar=document.getElementById('calendarJump'),dateStatus=document.getElementById('dateStatus'),anchors=[...document.querySelectorAll('.time-separator[data-date]')],dates=[...new Set(anchors.map(x=>x.dataset.date).filter(Boolean))];let matches=[],cursor=-1,dateCursor=-1;function refresh(){const term=q.value.trim().toLowerCase();for(const item of items)item.classList.remove('search-match','active-match');matches=term?items.filter(x=>x.dataset.search.includes(term)):[];for(const item of matches)item.classList.add('search-match');cursor=-1;count.textContent=term?(matches.length?'找到 '+matches.length+' 条':'没有结果'):'输入关键词检索';prev.disabled=next.disabled=!matches.length}function go(step){if(!matches.length)return;matches.forEach(x=>x.classList.remove('active-match'));cursor=(cursor+step+matches.length)%matches.length;matches[cursor].classList.add('active-match');matches[cursor].scrollIntoView({behavior:'smooth',block:'center'});count.textContent=(cursor+1)+' / '+matches.length}q.addEventListener('input',refresh);q.addEventListener('keydown',e=>{if(e.key==='Enter'){e.preventDefault();go(e.shiftKey?-1:1)}});prev.addEventListener('click',()=>go(-1));next.addEventListener('click',()=>go(1));document.getElementById('clearSearch').addEventListener('click',()=>{q.value='';refresh();q.focus()});function jumpDate(value){if(!dates.length)return;let index=dates.indexOf(value);if(index<0){index=dates.findIndex(x=>x>=value);if(index<0)index=dates.length-1}dateCursor=index;calendar.value=dates[index];const target=anchors.find(x=>x.dataset.date===dates[index]);target?.scrollIntoView({behavior:'smooth',block:'start'});dateStatus.textContent=dates[index]+' 的第一条时间分隔'}document.getElementById('jumpDate').addEventListener('click',()=>jumpDate(calendar.value));calendar.addEventListener('change',()=>jumpDate(calendar.value));document.getElementById('prevDate').addEventListener('click',()=>{if(!dates.length)return;dateCursor=dateCursor<0?dates.length-1:Math.max(0,dateCursor-1);jumpDate(dates[dateCursor])});document.getElementById('nextDate').addEventListener('click',()=>{if(!dates.length)return;dateCursor=dateCursor<0?0:Math.min(dates.length-1,dateCursor+1);jumpDate(dates[dateCursor])});refresh()})();</script></body></html>`;
  }

  function exportJson() {
    const data = exportData();
    const filename = `${archiveBaseName(data)}.json`;
    downloadBlob(new Blob([JSON.stringify(data, null, 2)], { type: 'application/json;charset=utf-8' }), filename);
    setStatus(`已导出 JSON：${data.messages.length} 条`, filename);
    return data;
  }

  function exportTxt() {
    const data = exportData();
    const filename = `${archiveBaseName(data)}.txt`;
    downloadBlob(new Blob(['\uFEFF', toTxt(data)], { type: 'text/plain;charset=utf-8' }), filename);
    setStatus(`已导出 TXT：${data.messages.length} 条`, filename);
    return data;
  }

  function exportHtml() {
    const data = exportData();
    const filename = `${archiveBaseName(data)}.html`;
    downloadBlob(new Blob(['\uFEFF', buildHtml(data)], { type: 'text/html;charset=utf-8' }), filename);
    setStatus(`已导出 HTML：${data.messages.length} 条`, '文本可离线查看；图片仍使用原始 URL');
    return data;
  }

  function blobToDataUrl(blob) {
    return new Promise((resolve, reject) => {
      const reader = new FileReader();
      reader.onload = () => resolve(reader.result);
      reader.onerror = () => reject(reader.error || new Error('读取图片数据失败'));
      reader.readAsDataURL(blob);
    });
  }

  function gmRequestBlob(url) {
    return new Promise((resolve, reject) => {
      if (typeof GM_xmlhttpRequest !== 'function') return reject(new Error('GM_xmlhttpRequest 不可用'));
      GM_xmlhttpRequest({
        method: 'GET', url, responseType: 'blob', timeout: 45000,
        onload: (response) => response.status >= 200 && response.status < 300
          ? resolve(response.response)
          : reject(new Error(`HTTP ${response.status}`)),
        onerror: () => reject(new Error('图片请求失败')),
        ontimeout: () => reject(new Error('图片请求超时'))
      });
    });
  }

  async function requestBlob(url) {
    let browserCacheError = null;
    if (state.config.preferBrowserCache) {
      try {
        const cachedResponse = await fetch(url, {
          cache: 'force-cache', credentials: 'omit', referrerPolicy: 'no-referrer'
        });
        if (!cachedResponse.ok) throw new Error(`HTTP ${cachedResponse.status}`);
        return cachedResponse.blob();
      } catch (error) {
        browserCacheError = error;
      }
    }
    if (typeof GM_xmlhttpRequest === 'function') return gmRequestBlob(url);
    if (browserCacheError) throw browserCacheError;
    const response = await fetch(url, { credentials: 'omit', referrerPolicy: 'no-referrer' });
    if (!response.ok) throw new Error(`HTTP ${response.status}`);
    return response.blob();
  }

  async function requestBlobWithRetry(url, onRetry) {
    let lastError = null;
    const attempts = Math.max(1, state.config.resourceRetries || 5);
    for (let attempt = 1; attempt <= attempts && !state.stopRequested; attempt += 1) {
      try {
        const blob = await requestBlob(url);
        if (!blob?.size) throw new Error('资源内容为空');
        return blob;
      } catch (error) {
        lastError = error;
        if (attempt >= attempts) break;
        onRetry?.(attempt + 1, attempts, error);
        await wait(Math.min(6000, 500 * (2 ** (attempt - 1))) + Math.floor(Math.random() * 250));
      }
    }
    if (state.stopRequested) throw new Error('用户停止了资源下载');
    throw lastError || new Error('资源下载失败');
  }

  function allMediaUrls(data) {
    const urls = [];
    const add = (item) => {
      if (item?.url && !item.url.startsWith('data:') && !urls.includes(item.url)) urls.push(item.url);
    };
    const addCards = (cards) => {
      for (const card of cards || []) {
        add(card.cover);
        add(card.authorAvatar);
      }
    };
    for (const message of data.messages) {
      for (const item of [...(message.images || []), ...(message.emojis || [])]) add(item);
      for (const item of [...(message.quote?.images || []), ...(message.quote?.emojis || [])]) add(item);
      for (const video of message.videos || []) { add({ url: video.url }); add({ url: video.posterUrl }); }
      for (const video of message.quote?.videos || []) { add({ url: video.url }); add({ url: video.posterUrl }); }
      addCards(message.cards);
      addCards(message.quote?.cards);
    }
    return urls;
  }

  async function mapConcurrent(items, limit, worker) {
    const results = new Array(items.length);
    let cursor = 0;
    async function run() {
      while (cursor < items.length && !state.stopRequested) {
        const index = cursor++;
        try { results[index] = await worker(items[index], index); }
        catch (error) { results[index] = { error }; }
      }
    }
    await Promise.all(Array.from({ length: Math.min(limit, items.length) }, run));
    return results;
  }

  async function exportHtmlEmbedded() {
    if (state.running) throw new Error('请先停止或等待采集完成。');
    const data = exportData();
    const urls = allMediaUrls(data);
    if (!urls.length) return exportHtml();
    const okay = confirm(`将尝试读取并内嵌 ${urls.length} 个图片/表情。文件可能很大，且失效 URL 或控制台跨域限制会导致个别图片无法内嵌。继续吗？`);
    if (!okay) return null;
    state.stopRequested = false;
    state.running = true;
    state.operation = 'embed-images';
    updateButtons();
    const imageMap = new Map();
    let finished = 0;
    let failed = 0;
    try {
      await mapConcurrent(urls, state.config.imageConcurrency, async (url) => {
        try {
          const blob = await requestBlobWithRetry(url, (attempt, attempts) => {
            setStatus(`图片重试 ${attempt}/${attempts}`, `正在重新读取：${url.slice(0, 90)}`);
          });
          imageMap.set(url, await blobToDataUrl(blob));
        } catch (error) {
          failed += 1;
          recordError(`图片内嵌失败：${url}`, error);
        } finally {
          finished += 1;
          setStatus(`正在内嵌图片：${finished}/${urls.length}`, `成功 ${imageMap.size}，失败 ${failed}；可点“停止”保留已成功部分`);
        }
      });
      const filename = `${archiveBaseName(data)}（内嵌图片）.html`;
      downloadBlob(new Blob(['\uFEFF', buildHtml(data, imageMap)], { type: 'text/html;charset=utf-8' }), filename);
      setStatus(`已导出内嵌图片 HTML`, `内嵌成功 ${imageMap.size}/${urls.length}，失败 ${failed}`);
      return { data, embedded: imageMap.size, failed };
    } finally {
      state.running = false;
      state.operation = null;
      updateButtons();
    }
  }

  function extensionFrom(url, type = '') {
    const mime = type.toLowerCase();
    if (mime.includes('png')) return 'png';
    if (mime.includes('webp')) return 'webp';
    if (mime.includes('gif')) return 'gif';
    if (mime.includes('avif')) return 'avif';
    if (mime.includes('jpeg') || mime.includes('jpg')) return 'jpg';
    if (mime.includes('mp4')) return 'mp4';
    if (mime.includes('webm')) return 'webm';
    if (mime.includes('quicktime')) return 'mov';
    if (mime.includes('mpegurl')) return 'm3u8';
    try {
      const ext = new URL(url).pathname.match(/\.([a-z0-9]{2,5})$/i)?.[1]?.toLowerCase();
      if (['png', 'webp', 'gif', 'avif', 'jpg', 'jpeg', 'mp4', 'webm', 'mov', 'm3u8'].includes(ext)) return ext === 'jpeg' ? 'jpg' : ext;
    } catch (_) { /* ignore */ }
    return 'jpg';
  }

  const CRC_TABLE = (() => {
    const table = new Uint32Array(256);
    for (let n = 0; n < 256; n += 1) {
      let value = n;
      for (let bit = 0; bit < 8; bit += 1) value = (value & 1) ? (0xEDB88320 ^ (value >>> 1)) : (value >>> 1);
      table[n] = value >>> 0;
    }
    return table;
  })();

  function crc32(bytes) {
    let crc = 0xFFFFFFFF;
    for (const byte of bytes) crc = CRC_TABLE[(crc ^ byte) & 0xFF] ^ (crc >>> 8);
    return (crc ^ 0xFFFFFFFF) >>> 0;
  }

  function dosDateTime(date = new Date()) {
    const year = Math.max(1980, date.getFullYear());
    return {
      time: ((date.getHours() & 31) << 11) | ((date.getMinutes() & 63) << 5) | ((Math.floor(date.getSeconds() / 2)) & 31),
      date: (((year - 1980) & 127) << 9) | (((date.getMonth() + 1) & 15) << 5) | (date.getDate() & 31)
    };
  }

  function writeU16(view, offset, value) { view.setUint16(offset, value, true); }
  function writeU32(view, offset, value) { view.setUint32(offset, value >>> 0, true); }

  function concatBytes(parts) {
    const total = parts.reduce((sum, part) => sum + part.length, 0);
    const output = new Uint8Array(total);
    let offset = 0;
    for (const part of parts) { output.set(part, offset); offset += part.length; }
    return output;
  }

  function makeZip(files) {
    const encoder = new TextEncoder();
    const localParts = [];
    const centralParts = [];
    let localOffset = 0;
    const stamp = dosDateTime();
    for (const file of files) {
      const name = encoder.encode(file.name.replace(/\\/g, '/'));
      const bytes = file.data instanceof Uint8Array ? file.data : encoder.encode(String(file.data));
      const checksum = crc32(bytes);
      const local = new Uint8Array(30 + name.length);
      const localView = new DataView(local.buffer);
      writeU32(localView, 0, 0x04034B50);
      writeU16(localView, 4, 20);
      writeU16(localView, 6, 0x0800);
      writeU16(localView, 8, 0);
      writeU16(localView, 10, stamp.time);
      writeU16(localView, 12, stamp.date);
      writeU32(localView, 14, checksum);
      writeU32(localView, 18, bytes.length);
      writeU32(localView, 22, bytes.length);
      writeU16(localView, 26, name.length);
      writeU16(localView, 28, 0);
      local.set(name, 30);
      localParts.push(local, bytes);

      const central = new Uint8Array(46 + name.length);
      const centralView = new DataView(central.buffer);
      writeU32(centralView, 0, 0x02014B50);
      writeU16(centralView, 4, 20);
      writeU16(centralView, 6, 20);
      writeU16(centralView, 8, 0x0800);
      writeU16(centralView, 10, 0);
      writeU16(centralView, 12, stamp.time);
      writeU16(centralView, 14, stamp.date);
      writeU32(centralView, 16, checksum);
      writeU32(centralView, 20, bytes.length);
      writeU32(centralView, 24, bytes.length);
      writeU16(centralView, 28, name.length);
      writeU16(centralView, 30, 0);
      writeU16(centralView, 32, 0);
      writeU16(centralView, 34, 0);
      writeU16(centralView, 36, 0);
      writeU32(centralView, 38, 0);
      writeU32(centralView, 42, localOffset);
      central.set(name, 46);
      centralParts.push(central);
      localOffset += local.length + bytes.length;
    }
    const centralDirectory = concatBytes(centralParts);
    const end = new Uint8Array(22);
    const endView = new DataView(end.buffer);
    writeU32(endView, 0, 0x06054B50);
    writeU16(endView, 4, 0);
    writeU16(endView, 6, 0);
    writeU16(endView, 8, files.length);
    writeU16(endView, 10, files.length);
    writeU32(endView, 12, centralDirectory.length);
    writeU32(endView, 16, localOffset);
    writeU16(endView, 20, 0);
    return new Blob([...localParts, centralDirectory, end], { type: 'application/zip' });
  }

  async function exportOfflinePackage() {
    if (state.running) throw new Error('请先停止或等待采集完成。');
    const data = exportData();
    const urls = allMediaUrls(data);
    if (!confirm(`将制作离线 ZIP：HTML 在根目录，${urls.length} 个媒体资源放在 images 文件夹。脚本会先尝试浏览器缓存，未命中或跨域受限时再读取原始 URL；制作期间会占用内存。继续吗？`)) return null;
    state.stopRequested = false;
    state.running = true;
    state.operation = 'offline-package';
    updateButtons();
    const imageMap = new Map();
    const files = [];
    let finished = 0;
    let failed = 0;
    try {
      await mapConcurrent(urls, state.config.imageConcurrency, async (url, index) => {
        try {
          const blob = await requestBlobWithRetry(url, (attempt, attempts) => {
            setStatus(`离线资源重试 ${attempt}/${attempts}`, `网络请求失败，正在重试第 ${attempt} 次`);
          });
          const name = `images/${String(index + 1).padStart(5, '0')}.${extensionFrom(url, blob.type)}`;
          files.push({ name, data: new Uint8Array(await blob.arrayBuffer()) });
          imageMap.set(url, name);
        } catch (error) {
          failed += 1;
          recordError(`离线资源保存失败：${url}`, error);
        } finally {
          finished += 1;
          setStatus(`制作离线包：${finished}/${urls.length}`, `已保存 ${imageMap.size}，失败 ${failed}；可点“停止”导出已完成部分`);
        }
      });
      const encoder = new TextEncoder();
      const baseName = archiveBaseName(data);
      files.unshift({ name: `${baseName}.html`, data: encoder.encode(`\uFEFF${buildHtml(data, imageMap)}`) });
      files.push({ name: `${baseName}.json`, data: encoder.encode(JSON.stringify(data, null, 2)) });
      files.push({ name: '说明.txt', data: encoder.encode(`打开“${baseName}.html”即可离线查看。\n图片资源位于 images 文件夹。\n成功保存：${imageMap.size}\n失败：${failed}\n失败资源在 HTML 中保留原网络地址，联网时仍可能显示。`) });
      const zip = makeZip(files);
      if (zip.size > 3.8 * 1024 * 1024 * 1024) throw new Error('离线包超过普通 ZIP 的安全大小限制，请改用“单独下载图片”。');
      const filename = `${archiveBaseName(data)}.zip`;
      downloadBlob(zip, filename);
      setStatus('离线 HTML 包已导出', `图片成功 ${imageMap.size}/${urls.length}，失败 ${failed}；解压后打开“${baseName}.html”`);
      return { data, saved: imageMap.size, failed, filename };
    } finally {
      state.running = false;
      state.operation = null;
      updateButtons();
    }
  }

  function gmDownload(url, filename) {
    return new Promise((resolve, reject) => {
      if (typeof GM_download !== 'function') return reject(new Error('GM_download 不可用'));
      GM_download({
        url, name: filename, saveAs: false,
        onload: resolve,
        onerror: (error) => reject(new Error(error?.error || 'GM_download 失败')),
        ontimeout: () => reject(new Error('下载超时'))
      });
    });
  }

  async function downloadImages() {
    if (state.running) throw new Error('请先停止或等待采集完成。');
    const data = exportData();
    const urls = allMediaUrls(data);
    if (!urls.length) {
      setStatus('没有识别到可下载的图片或表情');
      return { downloaded: 0, failed: 0 };
    }
    if (!confirm(`将下载 ${urls.length} 个图片/表情。浏览器或 Tampermonkey 可能询问是否允许多个下载。继续吗？`)) return null;
    state.stopRequested = false;
    state.running = true;
    state.operation = 'download-images';
    updateButtons();
    let downloaded = 0;
    let failed = 0;
    try {
      await mapConcurrent(urls, state.config.imageConcurrency, async (url, index) => {
        const base = `${archiveBaseName(data)}_图片_${String(index + 1).padStart(4, '0')}`;
        try {
          if (typeof GM_download === 'function') {
            await gmDownload(url, `${base}.${extensionFrom(url)}`);
          } else {
            const blob = await requestBlobWithRetry(url, (attempt, attempts) => {
              setStatus(`图片重试 ${attempt}/${attempts}`, `正在重新读取：${url.slice(0, 90)}`);
            });
            downloadBlob(blob, `${base}.${extensionFrom(url, blob.type)}`);
            await wait(160);
          }
          downloaded += 1;
        } catch (error) {
          failed += 1;
          recordError(`图片下载失败：${url}`, error);
        } finally {
          setStatus(`正在下载图片：${downloaded + failed}/${urls.length}`, `成功 ${downloaded}，失败 ${failed}；可点“停止”`);
        }
      });
      const manifest = { conversationTitle: data.conversationTitle, exportedAt: new Date().toISOString(), urls };
      downloadBlob(new Blob([JSON.stringify(manifest, null, 2)], { type: 'application/json;charset=utf-8' }), `${archiveBaseName(data)}_图片链接清单.json`);
      setStatus('图片下载完成', `成功 ${downloaded}/${urls.length}，失败 ${failed}；另存了 URL 清单`);
      return { downloaded, failed };
    } finally {
      state.running = false;
      state.operation = null;
      updateButtons();
    }
  }

  function exportAll() {
    exportJson();
    setTimeout(exportTxt, 220);
    setTimeout(exportHtml, 440);
  }

  function recordError(context, error) {
    const item = {
      time: new Date().toISOString(),
      context,
      message: error?.message || String(error)
    };
    state.errors.push(item);
    if (state.errors.length > 100) state.errors.shift();
    console.warn(`[${GLOBAL_NAME}] ${context}`, error);
  }

  function describeElement(el) {
    if (!el) return null;
    return {
      tag: el.tagName?.toLowerCase(),
      id: el.id || '',
      class: String(el.className || '').slice(0, 300),
      clientHeight: el.clientHeight,
      scrollHeight: el.scrollHeight,
      scrollTop: el.scrollTop,
      messageMatches: safeQueryAll(el, state.config.selectors.message).length,
      messageIdMatches: el.querySelectorAll?.('[data-message-id]')?.length || 0
    };
  }

  function diagnose() {
    const ranked = getScrollCandidates().map((el) => ({ el, score: scoreContainer(el) })).sort((a, b) => b.score - a.score).slice(0, 8);
    const result = {
      version: VERSION,
      url: location.href,
      title: document.title,
      configuredContainer: state.config.scrollContainerSelector || null,
      selectedContainer: describeElement(state.container || ranked[0]?.el),
      candidates: ranked.map(({ el, score }) => ({ score, ...describeElement(el) })),
      selectorMatchesInDocument: {
        messages: safeQueryAll(document, state.config.selectors.message).length,
        realMessageIds: document.querySelectorAll('[data-message-id]').length,
        timeCandidates: safeQueryAll(document, state.config.selectors.timeSeparator).length
      },
      sampleMessageHtml: safeQueryAll(document, state.config.selectors.message)[0]?.outerHTML?.slice(0, 4000) || null,
      errors: state.errors
    };
    console.group(`[${GLOBAL_NAME}] DOM 诊断`);
    console.log(result);
    console.table(result.candidates);
    console.info('如自动识别失败，可用：XHS_DM_EXPORTER.start({scrollContainerSelector:"你的选择器",selectors:{message:["你的消息选择器"],timeSeparator:["你的时间选择器"]}})');
    console.groupEnd();
    return result;
  }

  function createPanel() {
    if (state.panel?.isConnected) return state.panel;
    const style = document.createElement('style');
    style.id = 'xhs-dm-exporter-style';
    style.textContent = `#xhs-dm-exporter-panel{position:fixed;z-index:2147483647;right:16px;top:78px;width:310px;background:#fff;color:#222;border:1px solid #e2e4e8;border-radius:14px;box-shadow:0 8px 30px #0003;font:13px/1.45 system-ui,-apple-system,"PingFang SC","Microsoft YaHei",sans-serif;overflow:hidden}#xhs-dm-exporter-panel *{box-sizing:border-box}#xhs-dm-exporter-panel .xhead{display:flex;align-items:center;justify-content:space-between;padding:10px 12px;background:#ff2442;color:#fff;font-weight:700;cursor:move;user-select:none;touch-action:none}#xhs-dm-exporter-panel .xclose{border:0;background:transparent;color:#fff;font-size:18px;cursor:pointer}#xhs-dm-exporter-panel .xbody{padding:12px}#xhs-dm-exporter-panel .xstatus{font-weight:700;margin-bottom:3px}#xhs-dm-exporter-panel .xdetail{min-height:36px;color:#666;font-size:12px;margin-bottom:9px;overflow-wrap:anywhere}#xhs-dm-exporter-panel .xbuttons{display:grid;grid-template-columns:1fr 1fr;gap:6px}#xhs-dm-exporter-panel button{border:1px solid #d5d8de;background:#f7f8fa;color:#222;border-radius:8px;padding:7px 6px;cursor:pointer;font:inherit}#xhs-dm-exporter-panel button.wide{grid-column:1/-1}#xhs-dm-exporter-panel button:hover:not(:disabled){background:#eceff3}#xhs-dm-exporter-panel button.primary{background:#ff2442;border-color:#ff2442;color:#fff}#xhs-dm-exporter-panel button.warn{background:#fff4f5;border-color:#ff9aaa;color:#b00020}#xhs-dm-exporter-panel button:disabled{opacity:.45;cursor:not-allowed}#xhs-dm-exporter-panel .xfoot{margin-top:8px;font-size:11px;color:#8a8f98}`;
    document.documentElement.appendChild(style);
    const panel = document.createElement('section');
    panel.id = 'xhs-dm-exporter-panel';
    panel.innerHTML = `<div class="xhead"><span>小红书私信导出器 v${VERSION}</span><button class="xclose" title="隐藏">×</button></div><div class="xbody"><div class="xstatus">准备就绪</div><div class="xdetail">打开一个具体私信会话，然后点击“开始采集”。</div><div class="xbuttons"><button data-action="start" class="primary">快速采集</button><button data-action="stop" class="warn">停止</button><button data-action="offline" class="primary wide">导出离线 HTML 包（ZIP）</button><button data-action="txt">导出 TXT</button><button data-action="json">导出 JSON</button><button data-action="html">快速 HTML（联网图）</button><button data-action="embedded">单文件内嵌 HTML</button><button data-action="images">单独下载图片</button><button data-action="diagnose">DOM 诊断</button></div><div class="xfoot">离线包内含“昵称的私信记录.html”与 images 文件夹。</div></div>`;
    document.body.appendChild(panel);
    state.panel = panel;
    state.statusEl = panel.querySelector('.xstatus');
    state.detailEl = panel.querySelector('.xdetail');
    enablePanelDrag(panel);
    for (const button of panel.querySelectorAll('[data-action]')) state.buttons[button.dataset.action] = button;
    panel.querySelector('.xclose').addEventListener('click', () => { panel.style.display = 'none'; });
    state.buttons.start.addEventListener('click', () => collectAll().catch(() => {}));
    state.buttons.stop.addEventListener('click', stop);
    state.buttons.txt.addEventListener('click', exportTxt);
    state.buttons.json.addEventListener('click', exportJson);
    state.buttons.offline.addEventListener('click', () => exportOfflinePackage().catch((error) => setStatus('离线包导出失败', error.message, true)));
    state.buttons.html.addEventListener('click', exportHtml);
    state.buttons.embedded.addEventListener('click', () => exportHtmlEmbedded().catch((error) => setStatus('内嵌图片导出失败', error.message, true)));
    state.buttons.images.addEventListener('click', () => downloadImages().catch((error) => setStatus('图片下载失败', error.message, true)));
    state.buttons.diagnose.addEventListener('click', diagnose);
    updateButtons();
    return panel;
  }

  function enablePanelDrag(panel) {
    const handle = panel.querySelector('.xhead');
    if (!handle) return;
    handle.addEventListener('pointerdown', (event) => {
      if (event.button !== 0 || event.target.closest('button')) return;
      event.preventDefault();
      const rect = panel.getBoundingClientRect();
      const offsetX = event.clientX - rect.left;
      const offsetY = event.clientY - rect.top;
      panel.style.left = `${rect.left}px`;
      panel.style.top = `${rect.top}px`;
      panel.style.right = 'auto';
      panel.style.bottom = 'auto';

      const move = (moveEvent) => {
        const maxLeft = Math.max(0, window.innerWidth - panel.offsetWidth);
        const maxTop = Math.max(0, window.innerHeight - panel.offsetHeight);
        const left = Math.min(maxLeft, Math.max(0, moveEvent.clientX - offsetX));
        const top = Math.min(maxTop, Math.max(0, moveEvent.clientY - offsetY));
        panel.style.left = `${left}px`;
        panel.style.top = `${top}px`;
      };
      const finish = () => {
        document.removeEventListener('pointermove', move);
        document.removeEventListener('pointerup', finish);
        document.removeEventListener('pointercancel', finish);
      };
      document.addEventListener('pointermove', move);
      document.addEventListener('pointerup', finish);
      document.addEventListener('pointercancel', finish);
    });
  }

  function setStatus(status, detail = '', isError = false) {
    createPanel();
    state.statusEl.textContent = status;
    state.statusEl.style.color = isError ? '#b00020' : '';
    state.detailEl.textContent = detail;
  }

  function updateButtons() {
    if (!state.panel) return;
    const hasData = state.messages.size > 0;
    state.buttons.start.disabled = state.running;
    state.buttons.stop.disabled = !state.running;
    for (const key of ['txt', 'json', 'offline', 'html', 'embedded', 'images']) {
      state.buttons[key].disabled = !hasData || state.running;
    }
  }

  function showPanel() {
    createPanel().style.display = '';
  }

  function destroy() {
    stop();
    state.panel?.remove();
    document.getElementById('xhs-dm-exporter-style')?.remove();
    delete window[GLOBAL_NAME];
  }

  const api = {
    version: VERSION,
    start: collectAll,
    stop,
    exportAll,
    exportTXT: exportTxt,
    exportJSON: exportJson,
    exportHTML: exportHtml,
    exportOfflinePackage,
    exportHTMLEmbedded: exportHtmlEmbedded,
    downloadImages,
    diagnose,
    showPanel,
    destroy,
    getData: exportData,
    getState: () => ({
      running: state.running,
      operation: state.operation,
      stopRequested: state.stopRequested,
      messages: state.messages.size,
      visualMedia: state.visualMediaUrls.size,
      videos: state.videoUrls.size,
      parsedNodes: state.parsedNodeCount,
      timelineMerges: state.timelineMergeCount,
      timeSeparators: state.markers.size,
      rounds: state.rounds,
      errors: [...state.errors],
      container: describeElement(state.container)
    })
  };

  Object.defineProperty(window, GLOBAL_NAME, { value: api, configurable: true });
  createPanel();
  console.info(`[${GLOBAL_NAME}] v${VERSION} 已加载。打开具体会话后点击面板“开始采集”，或运行 XHS_DM_EXPORTER.start()`);
})();

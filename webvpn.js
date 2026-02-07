// 引入 Node.js 内置模块
import fs from 'node:fs'           // 文件系统操作
import https from 'node:https'     // HTTPS 客户端/服务端
import http from 'node:http'       // HTTP 客户端/服务端
import path from 'node:path'       // 路径处理
import cluster from 'node:cluster' // 多进程集群支持
// 引入第三方库
import { ZSTDDecompress } from 'simple-zstd' //用于解压 ZSTD 编码的响应
import chalk from 'chalk'          // 终端彩色输出
import Koa from 'koa'              // Koa Web 框架
import WebSocket, { WebSocketServer } from 'ws' // WebSocket 支持
import fetch, { File, FormData } from 'node-fetch' // 用于发起后端请求
import iconv from 'iconv-lite'     // 字符集转换（如 GBK 转 UTF-8）

// 引入自定义工具库
import { fsUtils } from '@wp1001/node'

// 创建一个忽略 SSL 证书错误的 HTTPS Agent，用于请求自签名证书的内部站点
const httpsAgent = new https.Agent({ rejectUnauthorized: false })

// 全局缓存对象，用于在多进程模式下同步数据
const globalCache = {
  cache: {},
  // 获取缓存
  getItem (key) {
    return globalCache.cache[key]
  },
  // 设置缓存，如果是工作进程，则发送消息给主进程进行同步
  setItem (key, value) {
    globalCache.cache[key] = value
    if (!cluster.isMaster) {
      process.send({ workerId: process.pid, action: 'setCache', key, value })
    }
  }
}

class WebVPN {
  constructor (config) {
    // 设置环境变量，允许连接不安全的 HTTPS 站点
    process.env.NODE_TLS_REJECT_UNAUTHORIZED = config.NODE_TLS_REJECT_UNAUTHORIZED || 0
    const { port, httpsPort, site, isYBMC } = config
    
    // 计算 VPN 的基础域名（去掉 www）
    config.vpnDomain = site.hostname.replace('www', '')
    // 构造 HTTP 和 HTTPS 的 VPN 完整入口地址
    config.httpVpnDomain = config.vpnDomain + ":25000"
    config.httpsVpnDomain = config.vpnDomain + ":25000"

    this.config = config
    // 定义支持处理的文件类型分类
    this.mimes = ['json', 'js', 'css', 'html', 'image', 'video', 'audio']
    // 正则表达式匹配文件扩展名到分类
    this.mimeRegs = [
      [/\.json/i, 'json'],
      [/\.js/i, 'js'],
      [/\.css/i, 'css'],
      [/\.wasm/i, 'wasm'],
      [/\.(png|jpg|ico|svg|gif|webp|jpeg)/i, 'image'],
      [/\.(mp4|m3u8|ts|flv)[^a-zA-Z]/i, 'video'],
      [/\.(mp3|wav|ogg)/i, 'audio'],
      [/\.(pdf|csv|tsv|doc|docx|xls|xlsx|ppt|pptx)/i, 'pdf-office'],
      [/\.(html|php|do|asp|htm|shtml)/i, 'html'],
      [/\.(ttf|eot|woff|woff2)/i, 'font']
    ]
    // MIME 类型字典，用于解析 Content-Type 头
    this.mimeDict = {
      'html': 'text/html',
      'text': 'text/plain',
      'js': 'application/javascript, application/x-javascript, text/javascript',
      'css': 'text/css',
      'image': 'image/png, image/jpg, image/jpeg, image/gif',
      'json': 'application/json',
      'video': 'video/mp4, application/vnd.apple.mpegurl',
      'audio': 'audio/webm, audio/mpeg',
      'pdf-office': 'application/pdf',
      'stream': 'application/octet-stream, application/protobuffer',
      'event-stream': 'text/event-stream'
    }
    // JavaScript 关键字列表，用于在沙箱环境中避免覆盖这些关键字
    this.jsKeywords = [
      'break', 'case', 'catch', 'continue', 'default', 'delete', 'do', 'else', 'finaly', 'for',
      'function', 'if', 'in', 'instanceof', 'new', 'return', 'switch', 'this', 'throw', 'try',
      'typeof', 'var', 'void', 'while', 'with',
      'boolean', 'byte', 'char', 'class', 'const', 'debugger', 'double', 'enum', 'export',
      'extends', 'final', 'float', 'goto', 'implements', 'import', 'int', 'interface', 'long',
      'native', 'package', 'private', 'protected', 'public', 'short', 'static', 'super',
      'synchronized', 'throws', 'transient', 'volatile'
    ]
    // 请求头黑名单：请求转发时需要删除这些头
    this.ignoreRequestHeaderRegexps = [
      /^x-(forwarded|requested|csrf|content|frame)/i,
      /upgrade-insecure-requests/i
    ]
    // 响应头黑名单：返回给客户端时需要删除这些头
    this.ignoreResponseHeaderRegexps = [
      /content-length/i, // 删除长度，因为内容可能被修改（重写URL）导致长度变化
      /x-content-type-options/i,
      /report-to/i,
      /x-xss-protection/i,
      /cross-origin-resource-policy/i,
      /cross-origin-opener-policy/i,
      /cross-origin-embedder-policy/i,
      /content-security-policy-report-only/i,
    ]

    // 不需要进行内容转换（重写）的类型
    this.noTransformMimes = ['wasm', 'font', 'json', 'image', 'video', 'audio', 'pdf-office', 'stream', 'event-stream']
    // 需要缓存的文件类型
    this.cacheMimes = ['js', 'css', 'font', 'image', 'video', 'audio', 'pdf-office']
    this.cacheDir = config.cacheDir || 'cache'

    // 初始化检查缓存目录
    this.checkCaches()

    // 读取前端拦截脚本
    this.jsInterceptCode = fs.readFileSync('./public/intercept.js')

    // 定义域名转换的前端 JS 代码（注入到浏览器中执行）
    // 用于将真实域名 (google.com) 转换为 VPN 内部域名 (google-com.vpn.site)
    this.convertDomainsCode = `
      const httpVpnDomain = '${config.httpVpnDomain}'
      const httpsVpnDomain = '${config.httpsVpnDomain}'
      const httpsEnabled = '${config.httpsEnabled}'
      const subdomains = ${JSON.stringify(config.subdomains)}
      const domainDict = {}
      const domainMode = '${config.domainMode}'
      // 构建域名映射字典
      Object.entries(subdomains).forEach(([sub, name]) => domainDict[name] = sub)
      
      // 原始模式的编码/解码函数（可能基于冒号替换）
      const _encode_host_original_ = text => {
        return domainDict[text] || text.replace(':', '_._')
      }
      const _decode_host_original_ = text => {
        return subdomains[text] || text.replace('_._', ':')
      }
      
      // 下划线模式的编码/解码函数（将点号换成双下划线等，避免多级域名问题）
      const _encode_host_underline_ = text => {
        let value = domainDict[text]
        if (!value) {
          value = text.replaceAll('.', '__').replaceAll('-', '_h_').replace(':', '_c_')
        }
        return value
      }
      const _decode_host_underline_ = text => {
        let value = subdomains[text]
        if (!value) {
          value = text.replace('_c_', ':').replaceAll('_h_', '-').replaceAll('__', '.')
        }
        return value
      }
      // 根据配置挂载全局函数
      globalThis.encodeHost = domainMode === 'underline' ? _encode_host_underline_ : _encode_host_original_
      globalThis.decodeHost = domainMode === 'underline' ? _decode_host_underline_ : _decode_host_original_
    `
    // 在服务端也执行一遍，以便服务端代码可以直接使用 encodeHost/decodeHost
    eval(this.convertDomainsCode)

    // 定义注入到 Web Worker 中的代码上下文
    // 用于拦截 Worker 内部的 fetch 和 importScripts 请求
    this.jsWorkerContextCode = `
      // worker 里面创造 __context__ 环境
      if (!self.window) {
        // 绑定定时器函数
        setTimeout = self.setTimeout.bind(self)
        setInterval = self.setInterval.bind(self)
        clearTimeout = self.clearTimeout.bind(self)
        clearInterval = self.clearInterval.bind(self)
        
        // 劫持 importScripts，重写导入的 URL
        const _importScripts  = self.importScripts
        self.importScripts = function (...props) {
          props = props.map(transformUrl)
          return _importScripts.apply(self, props)
        }
        
        const target = new URL('#targetUrl#') // 目标真实 URL
        const site = new URL('#siteUrl#')     // VPN 站点 URL
        
        // URL 转换函数：将真实 URL 转为 VPN 代理 URL
        function transformUrl (url) {
          url = (url ? url.toString() : '').trim()
          if (url.startsWith('//')) {
            url = target.protocol + url
          } else if (url.startsWith('/')) {
            url = new URL(url, target.href).href
          }
          const u = new URL(url)
          if (httpsEnabled){
              u.host = encodeHost(u.host) + httpsVpnDomain
          }
          else{
              u.host = encodeHost(u.host) + (u.protocol === 'http:' ? httpVpnDomain : httpsVpnDomain)
          }
          u.searchParams.set("__webvpn_origin_scheme__", u.protocol.slice(0, -1))
          u.protocol = httpsEnabled ? "https:" : "http:"
          if (u.host.includes(vpnDomain)) return url // 已经是 VPN 域名则不处理
          console.log('in inject: ', u.toString())
          return u.toString()
        }

        self.webvpn = { target, site, transformUrl }
        const globalCons = ['self', 'globalThis']
        // 需要模拟的 location 属性
        const locationAttrs = ['hash', 'host', 'hostname', 'href', 'origin', 'pathname', 'port', 'protocol', 'search']

        // 构造虚拟的 location 对象
        self.__location__ = {}
        locationAttrs.forEach(key => {
          self.location['__' + key + '__'] = webvpn.target[key]
          // 双重定义，确保通过不同方式访问都能获取到虚拟值
          for (let i = 0; i < 2; i++) {
            if (i) key = '__' + key + '__'
            Object.defineProperty(self.__location__, key, {
              get () {
                key = key.replaceAll('__', '')
                return webvpn.target[key] || location[key]
              }
            })
          }
        })
        self.__location__.toString = () => self.__location__.href

        // 代理全局对象 (self, globalThis)，拦截属性访问
        for (const con of globalCons) {
          if (con === 'globalThis') {
            self['__' + con + '__'] = self.__self__
            continue
          }
          self['__' + con + '__'] = new Proxy(self[con], {
            get (target, property, receiver) {
              // 访问 location 或全局对象时返回代理后的对象
              if (globalCons.includes(property) || property === 'location') {
                return self['__' + property + '__']
              }
              const value = target[property]
              return (typeof value === 'function' && !value.prototype) ? value.bind(target) : value
            },
            set (target, property, value) {
              // 禁止修改全局核心对象
              if (['globalThis', 'self', 'location'].includes(property)) {
                return false
              }
              target[property] = value
              return true
            }
          })
        }
        // 创建执行上下文对象
        self.__context__ = {
          self: self.__self__,
          globalThis: self.__globalThis__,
          location: self.__location__
        }
        // 创建上下文代理，用于 with 语句
        self.__context_proxy__ = new Proxy(self.__context__, {
          has (target, prop) {
            return true // 拦截所有属性检查
          },
          get (target, prop) {
            return prop in target ? target[prop] : self[prop]
          },
          set (target, prop, value) {
            self[prop] = value
            return value
          }
        })

        // 劫持 fetch API，重写请求 URL
        const fetch = self.fetch
        self.fetch = function (input, init) {
          if (input instanceof URL) input = input.href
          const isInputUrl = typeof input === 'string'
          const url = isInputUrl ? input : input.url
          const newUrl = transformUrl(url) // 重写 URL
          if (isInputUrl) {
            input = newUrl
          } else {
            // 如果输入是 Request 对象，需克隆并修改 URL
            const init = {}
            for (let key in input) {
              const value = input[key]
              if (key === 'url' || typeof value === 'function') continue
              if (key === 'mode' && value === 'navigate') continue
              init[key] = value
            }
            input = new Request(newUrl, init)
          }
          return fetch.apply(self, [input, init])
        }
      }
    `
    // JS 代码作用域前缀：利用 with 语法实现沙箱隔离
    this.jsScopePrefixCode = `
    (function () {
      atob = self.atob.bind(self)
      addEventListener = self.addEventListener.bind(self)
      if (self.postMessage) {
        postMessage = self.postMessage.bind(self)
      }
      // 进入代理上下文，所有的全局变量访问都会先经过 __context_proxy__
      with (self.__context_proxy__) {
    `
    // JS 代码作用域后缀
    this.jsScopeSuffixCode = `
    }).call(self.__context__.self)
    `

    this.public = []
    this.initPublic() // 初始化公共静态资源列表
  }

  // 检查并加载缓存目录结构
  async checkCaches () {
    if (this.config.cache) {
      this.caches = { }
      const dirs = await fsUtils.listDir(this.cacheDir)
      dirs.forEach(async dir => {
        this.caches[dir] = await fsUtils.listDir(path.join(this.cacheDir, dir))
      })
    }
  }

  // 初始化 public 目录下的文件列表
  async initPublic () {
    fsUtils.listDir('public').then(files => {
      this.public = files.map(file => path.join('public', file))
    })
  }

  // 启动服务
  start () {
    // 如果配置了多进程且当前是主进程，则进行 Fork
    if (this.config.numProcesses > 1 && cluster.isMaster) {
      for (let i = 0; i < this.config.numProcesses; i++) {
        cluster.fork()
      }
      cluster.on('listening', (worker, address) => {
        // 监听 Worker 消息，实现缓存同步
        worker.on('message', ({ action, key, value, workerId }) => {
          if (action === 'setCache') {
            const params = { action: 'syncCache', key, value }
            // 广播给其他 Worker
            for (let key in cluster.workers) {
              if (key === workerId) continue
              cluster.workers[key].send(params)
            }
          }
        })
        console.log(chalk.green(`listening: worker ${worker.process.pid} - Address: ${address.address}:${address.port}`))
      })
      // 进程退出后自动重启
      cluster.on('exit', (worker, code, signal) => {
        console.log(chalk.yellow(`工作进程 ${worker.process.pid} 关闭 ${signal || code}. 重启中...`) + '\n')
        cluster.fork()
      })
    } else {
      // Worker 进程或单进程模式下创建应用
      this.createApp()
      if (!cluster.isMaster) {
        // 接收主进程的同步缓存消息
        process.on('message', ({ action, key, value }) => {
          if (action === 'syncCache') {
            globalCache.cache[key] = value
          }
        })
      }
    }
  }

  // 处理主站请求 (www子域名)
  async serveWww (ctx) {
    if (ctx.url === '/') {
      // 返回首页 index.html
      ctx.res.writeHead(200, { 'Content-Type': 'text/html' })
      let text = await fsUtils.read(path.join('public', 'index.html'))
      // 注入配置信息到首页
      text = text.replace(
        `'inject_code'`,
        'const config = ' + JSON.stringify(this.config, null, 2) + '\n' + this.convertDomainsCode
      )
      ctx.body = text
    } else if (ctx.url.startsWith('/share-sessions')) {
      // 处理会话共享逻辑
      if (ctx.method === 'POST') {
        const body = await this.calcRequestBody(ctx)
        await globalCache.setItem(ctx.query.shareId + '-clientCache', body)
      }
      return ctx.res.writeHead(200, {
        'access-control-allow-credentials': true,
        'access-control-allow-origin': ctx.headers['origin'] || '*',
        'access-control-allow-headers': '*',
        'access-control-allow-methods': '*'
      })
    } else {
      // 检查是否请求 public 目录下的静态文件
      await this.checkPublic(ctx)
    }
  }

  // 检查并响应 public 目录的静态文件
  async checkPublic (ctx) {
    const parts = ctx.url.split('/public/')
    let filepath = parts[1] && path.join('public', parts[1]) || ''
    filepath = filepath.split('?')[0]

    if (this.public.includes(filepath)) {
      await this.respondFile(ctx, filepath)
      return true
    }
    return false
  }

  // 尝试从本地文件系统获取缓存的响应
  async getCache (ctx) {
    const { host, pathname } = ctx.meta.target
    const filename = encodeURIComponent(pathname)
    if (!this.caches[host] || !this.caches[host].includes(filename)) {
      return null
    }
    await this.respondFile(ctx, path.join(this.cacheDir, host, filename))
    return true
  }

  // 将响应写入本地缓存
  async setCache (ctx, res) {
    if (
      !this.config.cache
      || !this.cacheMimes.includes(ctx.meta.mime)
      || !res.data
      || ctx.meta.cache === false
    ) {
      return
    }

    const { host, pathname } = ctx.meta.target
    const dir = path.join(this.cacheDir, host)
    if (!await fsUtils.exists(dir)) {
      await fsUtils.mkdir(dir)
    }
    await fsUtils.write(path.join(dir, encodeURIComponent(pathname)), res.data)
  }

  // 创建 Koa 应用实例
  createApp () {
    const { config } = this
    const app = new Koa()
    app.use(this.proxyRoute.bind(this)) // 挂载核心代理中间件

    const server = http.createServer({}, app.callback())

    // 创建 WebSocket 服务
    this.wsServer = new WebSocketServer({ server })
    this.wsServer.onConnection = async (client, request) => {
      // 处理 WebSocket 连接
      let { host, origin } = request.headers
      if (host) host = this.convertHost(host) // 还原真实 Host
      const protocol = origin && !origin.startsWith('https') ? 'http' : 'https'
      const url = protocol + '://' + host + (request.url || '') // 构造真实 WS 地址

      const wsClient = new WebSocket(url) // 连接目标 WebSocket
      await new Promise(resolve => {
        wsClient.on('open', resolve)
      })
      // 双向转发消息
      wsClient.on('message', message => {
        message = message.toString()
        client.send(message)
      })
      wsClient.on('close', () => {
        client.close()
      })

      client.on('message', message => {
        message = message.toString()
        wsClient.send(message)
      })
      client.on('close', () => {
        wsClient.close()
      })
    }

    server.listen(config.port)

    // 如果启用了 HTTPS，则加载证书并启动 HTTPS 服务
    if (config.httpsEnabled) {
      const options = {
        key: fs.readFileSync('ssl/server.key'),
        cert: fs.readFileSync('ssl/server.pem')
      }
      https.createServer(options, app.callback()).listen(config.httpsPort)
    }
  }

  // 核心路由代理逻辑
  async proxyRoute (ctx, next) {
    console.log("in proxyRoute")
    const { httpVpnDomain, httpsVpnDomain, site } = this.config
    // 处理 WebSocket 升级请求
    if (ctx.headers.upgrade === 'websocket') {
      this.wsServer.handleUpgrade(ctx.request, ctx.socket, ctx.headers, client => {
        this.wsServer.onConnection(client, ctx.request)
      })
    }
    console.log(new URL(ctx.request.href).searchParams)
    // 确定当前请求协议 (http/https)
    if (new URL(ctx.request.href).searchParams.get("__webvpn_origin_scheme__")){
        ctx.scheme = new URL(ctx.request.href).searchParams.get("__webvpn_origin_scheme__")
        console.log("use url param, set scheme to: ", ctx.scheme)
    }
    else {
        ctx.scheme = new URL(ctx.request.href).protocol.slice(0, -1)
    }
    console.log("scheme is: ", ctx.scheme)
    const vpnDomain = ctx.scheme === 'http' ? httpVpnDomain : httpsVpnDomain
    // 提取子域名
    let subdomain = ctx.headers.host.replace(vpnDomain, '')
    console.log(subdomain)
    if (subdomain === 'www') {
      return await this.serveWww(ctx) // 访问主页
    } else {
      // 如果子域名直接以 vpnDomain 开头，可能是错误的请求，重定向回主站
      if (subdomain.split('-')[0] === vpnDomain.slice(1)) {
        ctx.res.writeHead(302, {
          location: ctx.scheme + '://' + site.host
        })
        return
      }
    }
    ctx.subdomain = subdomain

    // 检查是否为公共资源
    const isPublic = await this.checkPublic(ctx)
    if (isPublic) {
      return
    }

    // 初始化路由元数据（解码真实域名等）
    await this.routeInit(ctx)

    console.log(ctx.request.href)

    // 检查是否有缓存
    if (this.config.cache && ctx.meta.cache !== false) {
      if (await this.getCache(ctx)) {
        return
      }
    }

    // 如果是不需要转换的类型（如图片/视频），直接流式管道转发
    if (this.noTransformMimes.includes(ctx.meta.mime)) {
      return await this.respondPipe(ctx)
    }

    let res = null
    try {
      // 发起代理请求，获取完整内容
      res = await this.request(ctx)
    } catch (err) {
      ctx.body = err
      return
    }
    if (res === true) return // 可以在 request 内部处理完直接返回 true

    // 清理响应头
    this.deleteIgnoreHeaders(this.ignoreResponseHeaderRegexps, res.headers)
    Object.keys(res.headers).forEach(key => ctx.set(key, res.headers[key]))

    // 如果是重定向状态码，直接返回
    if (res.status >= 300 && res.status < 400) {
      ctx.body = res.data
      return
    }

    // 针对 HTML 内容的修正判断：如果内容看起来像 JSON，则强制改为 JSON 处理
    if (ctx.meta.mime === 'html') {
      const firstChar = res.data[0]
      const lastChar = res.data[res.data.length - 1]
      if (
        firstChar === '[' && lastChar === ']'
        || firstChar === '{' && lastChar === '}'
      ) {
        ctx.meta.mime = 'json'
        ctx.meta.done = true
      } else if (!/<[a-zA-Z]+/.test(res.data)) {
        ctx.meta.mime = 'text'
        ctx.meta.done = true
      }
    }

    // 调用请求后钩子
    if (!ctx.meta.done && (await this.afterRequest(ctx, res))) {
      return
    }

    // 核心重写逻辑：替换 URL，注入脚本等
    if (!ctx.meta.done && res.data && this.shouldReplaceUrls(ctx, res)) {
      this.replaceUrls(ctx, res) // 替换 HTML/CSS 中的链接
      this.customResponse(ctx, res) // 自定义响应处理（如去除 use strict）
      if (ctx.meta.mime === 'html') {
        res.data = this.processHtml(ctx, res) // 处理 CSP 等
        res.data = this.processHtmlScopeCodes(ctx, res.data) // 处理 HTML 中的内联脚本
        if (!ctx.meta.isXHR) {
          res.data = await this.appendScript(ctx, res) // 注入 VPN 客户端脚本
        }
      } else if (ctx.meta.mime === 'js') {
        res.data = this.processJsScopeCode(ctx, res.data) // 处理 JS 文件
      }
    }

    // 处理 SourceMap 等其他杂项
    if (!ctx.meta.done) {
      this.processOthers(ctx, res)
    }

    // 响应前钩子
    if (!ctx.meta.done && this.beforeResponse(ctx, res)) {
      return
    }

    // 写入缓存
    this.setCache(ctx, res)

    // 发送最终响应体
    ctx.body = res.data
  }

  // 初始化路由信息
  async routeInit (ctx) {
    // 检查是否包含共享会话 ID (shareId)
    const { isMainSession, shareId } = await this.checkShareSession(ctx)
    const domain = decodeHost(ctx.subdomain) // 解码出真实域名
    const url = ctx.scheme + '://' + domain + ctx.url
    // 构建元数据对象
    ctx.meta = {
      shareId,
      isMainSession,
      url,
      isXHR: ctx.request.headers['x-requested-with'] === 'XMLHttpRequest',
      mime: this.getResponseType(ctx, url), // 推断响应类型
      scheme: ctx.scheme,
      target:  new URL(url), // 目标 URL 对象
      host: ctx.headers['host'],
      origin: ctx.headers['origin'],
      referer: ctx.headers['referer']
    }
  }

  // 检查 URL 中是否包含会话共享信息
  async checkShareSession (ctx) {
    let isMainSession = false, shareId = ''
    // 解析 subdomain 中的 shareId (例如: google-com-main-xxxxxx)
    if (!ctx.subdomain.includes('.') && ctx.subdomain.includes('-')) {
      const parts = ctx.subdomain.split('-')
      ctx.subdomain = parts[0] // 还原真实子域名部分
      isMainSession = parts[1] === 'main'
      shareId = parts[2]
      const shareSuffix = '-' + parts.slice(1).join('-')
      // 清理 Header 中的 share 后缀
      for (let key of ['host', 'origin', 'referer']) {
        if (ctx.headers[key]) {
          ctx.headers[key] = ctx.headers[key].replace(shareSuffix, '')
        }
      }
      // 如果是主会话，保存 Cookie/Auth 到缓存
      if (isMainSession) {
        if (ctx.headers['cookie']) {
          await globalCache.setItem(shareId + '-cookie', ctx.headers['cookie'])
        }
        if (ctx.headers['authorization']) {
          await globalCache.setItem(shareId + '-authorization', ctx.headers['authorization'])
        }
      } else {
        // 如果是共享会话，从缓存读取 Cookie/Auth 并注入
        const cookie = await globalCache.getItem(shareId + '-cookie')
        const authorization = await globalCache.getItem(shareId + '-authorization')
        if (cookie) ctx.headers['cookie'] = cookie
        if (authorization) ctx.headers['authorization'] = authorization
      }
    }
    // 清理 Origin/Referer 中的子域名后缀
    for (let key of ['origin', 'referer']) {
      if (ctx.headers[key]?.includes('-')) {
        const subdomain = new URL(ctx.headers[key]).host.split('.')[0]
        if (subdomain.includes('-')) {
          ctx.headers[key] = ctx.headers[key].replace('-' + subdomain.split('-').slice(1).join('-'), '')
        }
      }
    }
    return { isMainSession, shareId }
  }

  // 响应本地文件
  async respondFile (ctx, filepath) {
    ctx.res.writeHead(200)
    const stream = fs.createReadStream(filepath)
    await new Promise(resolve => {
      stream.pipe(ctx.res)
      stream.on('end', resolve)
    })
  }

  // 管道式转发响应 (用于大文件、流媒体等不需要修改内容的资源)
  async respondPipe (ctx) {
    const headers = { ...ctx.headers }
    this.setOriginHeaders(ctx, headers) // 重写 Origin/Referer
    this.deleteIgnoreHeaders(this.ignoreRequestHeaderRegexps, headers) // 删除黑名单头

    const method = ctx.request.method.toLowerCase()
    const { protocol, hostname, port } = ctx.meta.target

    const isHttps = protocol.startsWith('https')
    const options = {
      url: ctx.meta.url,
      method,
      protocol,
      hostname,
      headers,
      path: ctx.meta.url.slice(protocol.length + 2 + hostname.length + (port ? port.length + 1 : 0)), // 提取 Path
      port: port * 1 || (isHttps ? 443 : 80)
    }
    if (isHttps && !options.agent) {
      options.agent = httpsAgent // 使用忽略证书的 Agent
    }
    const result = await this.beforeRequest(ctx, options)
    if (result) return result
    // 使用原生 http/https 模块发起请求并 pipe 响应
    await new Promise(resolve => {
      const lib = isHttps ? https : http
      const req = lib.request(options, async res => {
        const headers = await this.initResponseHeaders(ctx, res)
        this.deleteIgnoreHeaders(this.ignoreResponseHeaderRegexps, headers)
        ctx.res.writeHead(res.statusCode, headers)
        res.pipe(ctx.res)
        res.on('end', resolve)
      })
      req.on('error', err => {
        ctx.res.writeHead(500)
        ctx.body = err
      })
      req.end()
    })
  }

  // 发起普通请求 (获取内容到内存中以便修改)
  async request (ctx) {
    const { method, header } = ctx.request
    this.deleteIgnoreHeaders(this.ignoreRequestHeaderRegexps, header)
    this.setOriginHeaders(ctx, header)

    const options = {
      url: ctx.meta.url,
      method,
      headers: header,
      redirect: 'manual', // 手动处理重定向
      ...this.getRequestOptions(ctx)
    }
    // 如果有请求体，读取并转发
    if (method === 'POST' || method === 'PUT' || method === 'PATCH') {
      options.body = await this.calcRequestBody(ctx)
    }
    console.log("fetch url: ", options.url);
    console.log("fetch body: ", options.body)
    const result = await this.beforeRequest(ctx, options)
    if (result) return result
    try {
      return await this.fetchRequest(ctx, options)
    } catch (err) {
      const msg = 'request failed: ' + ctx.meta.url + '\n' + err.toString()
      console.log(chalk.red(msg) + '\n')
      throw msg
    }
  }

  // 读取请求体数据
  async calcRequestBody (ctx) {
    const hasFile = ctx.headers['content-type']?.includes('multipart/form-data; boundary')
    let body = hasFile ? [] : ''
    await new Promise(resolve => {
      ctx.req.on('data', chunk => {
        if (hasFile) {
          body.push(...chunk)
        } else {
          body += chunk
        }
      })
      ctx.req.on('end', resolve)
    })
    // 如果是文件上传，重新封装为 FormData
    if (hasFile) {
      const formData = new FormData()
      formData.append(undefined, new File([new Uint8Array(body)], undefined, {}))
      body = formData
    }
    return body
  }

  // 使用 node-fetch 执行请求
  async fetchRequest (ctx, options) {
    const res = await fetch(ctx.meta.url, options)
    const headers = await this.initResponseHeaders(ctx, res)

    // 如果是重定向，直接返回 Header 即可
    if (headers.location) {
      ctx.res.writeHead(res.status, headers)
      ctx.meta.done = true
      return { status: res.status, headers }
    }

    let data = ''
    ctx.meta.mime = this.getMimeByResponseHeaders(headers) || ctx.meta.mime

    // 如果发现不需要转换的 MIME 类型（且没有走 respondPipe），直接透传
    if (this.noTransformMimes.includes(ctx.meta.mime)) {
      if (headers['content-encoding']?.includes('gzip')) {
        delete headers['content-encoding'] // 解压交给 node-fetch 或后续处理
      }
      ctx.meta.done = true
      // 如果是 JSON，读取文本返回
      if (ctx.meta.mime === 'json') {
        delete headers['content-encoding']
        data = await res.text()
        if (data === '') data = '{}'
        return {
          status: res.status,
          data,
          headers
        }
      }
      // 其他二进制流，pipe 回去
      ctx.res.writeHead(res.status, headers)
      res.body.pipe(ctx.res)
      await new Promise((resolve) => {
        res.body.on('end', resolve)
      })
    } else {
      ctx.status = res.status
      delete headers['content-encoding']
      // 核心：处理字符集，转为 UTF-8 字符串
      data = await this.convertCharsetData(ctx, headers, res)
      // 如果是 JSONP 或 JSON，直接返回
      if (this.isJsonpResponse(data, ctx) || this.isJsonResponse(data, ctx)) {
        ctx.body = data
        ctx.meta.done = true
      }
    }
    return {
      status: res.status,
      data,
      headers
    }
  }

  // 替换响应内容中的 URL
  replaceUrls (ctx, res) {
    const { mime } = ctx.meta
    const matches = []
    // 获取 Base URL
    ctx.meta.base = this.getBase(ctx, res)
    // 提取 HTML 中的链接
    if (mime === 'html') {
      matches.push(...this.getHtmlLinkMatches(ctx, res))
    }
    // 提取 CSS 中的链接 (url(...), @import)
    if (['html', 'css'].includes(mime)) {
      matches.push(...this.getCssUrlMatches(ctx, res))
    }
    // 执行替换
    res.data = this.replaceMatches(ctx, res, matches)
  }

  // 获取 HTML 中的 <base> 标签路径，如果没有则使用当前路径
  getBase (ctx, res) {
    const match = res.data.match(/\<base\s+href=(\"|\')[^\"\']+/)
    if (match) {
      const text = match[0]
      const index = Math.max(text.indexOf('"'), text.indexOf('\''))
      return text.slice(index + 1)
    }
    return ctx.meta.target.pathname.split('/').slice(0, -1).join('/') + '/'
  }

  // 正则匹配 HTML 中的 href, src, action 等属性
  getHtmlLinkMatches (ctx, res) {
    // return [...new Set(res.data.match(/\s(href|src|action|srcset|poster)=(\"|\')?(http\:|https\:|http\%3A|https\%3A|\/\/)[^\s\>]*/g))]
    // return [...new Set(res.data.match(/\s(href|src|action|srcset|poster)=(\"|\')?[^\s\>]*/g))]
    return [
      ...new Set(
        [...res.data.matchAll(/\s(?:href|src|action|srcset|poster)=((["'])?[^\s>]+)\2?/g)]
          .map(m => m[1])
      )
    ]
  }

  // 正则匹配 CSS 中的 url() 和 @import
  getCssUrlMatches (ctx, res) {
    // return [
    //   ...new Set(res.data.match(/url\([\"\']?[^\"\')]+/g)),
    //   ...new Set(res.data.match(/@import\s[\"\'][^\"\']+/g))
    // ]
    return [
      ...new Set([
        // url(...)
        ...[...res.data.matchAll(/url\((["'])?([^"')]+)\1?\)/g)]
          .map(m => m[2]),
    
        // @import "..."
        ...[...res.data.matchAll(/@import\s+(["'])([^"']+)\1/g)]
          .map(m => m[2])
      ])
    ]
  }

  // 执行具体的字符串替换操作
  replaceMatches (ctx, res, matches) {
    const { httpVpnDomain, httpsVpnDomain } = this.config
    const dict = {}
    // 过滤掉已经是 VPN 域名的链接
    matches.filter(m => {
      return !m.includes('\n') && m.indexOf(httpVpnDomain) < 0 && m.indexOf(httpsVpnDomain) < 0
    }).forEach(match => {
      if (match.startsWith('"') || match.startsWith("'")){
        match = match.slice(1,-1)
      }
      console.log("replace matches: ", match)
      dict[match] = this.transformUrl2(ctx, match)
      console.log("key: ", match, " value: ", dict[match])
    })
    // 按长度降序排列，优先替换长链接，防止部分替换
    Object.entries(dict).sort((a, b) => b[0].length - a[0].length).forEach(ele => {
      const [key, value] = ele
      console.log("replace ", key, " to ", value)
      res.data = res.data.replaceAll(key, value)
    })
    return res.data
  }
  // // 执行具体的字符串替换操作
  // replaceMatches (ctx, res, matches) {
  //   const { httpVpnDomain, httpsVpnDomain } = this.config
  //   const dict = {}
  //   // 过滤掉已经是 VPN 域名的链接
  //   matches.filter(m => {
  //     return !m.includes('\n') && m.indexOf(httpVpnDomain) < 0 && m.indexOf(httpsVpnDomain) < 0
  //   }).forEach(match => {
  //     console.log("replace matches: ", match)
  //     console.log(ctx.scheme, ctx.meta.scheme)
  //     let url = ''
  //     let prefix = ''
  //     let quote = ''
  //     // 解析链接部分
  //     if (match.slice(0, match.indexOf('//')).indexOf('http') >= 0) {
  //       url = match.slice(match.indexOf('http'), -1)
  //       prefix = match.indexOf('https') > 0 ? 'https://' : 'http://'
  //     } else {
  //       url = ctx.meta.scheme + ':' + match.slice(match.indexOf('//'), -1)
  //       quote = match[match.indexOf('//') - 1]
  //       prefix = '//'
  //     }
  //     const u = url.slice(url.indexOf('//') + 2)
  //     if (!u || !/[\w]+\./.test(u)) return
  //     // 处理 HTML 实体编码
  //     if (/&#x\w+;/.test(url)) {
  //       url = url.replaceAll(/&#x\w+;/g, ele => String.fromCharCode(parseInt(ele.slice(3, -1), 16)))
  //     }
  //     if (url.includes('"')) {
  //       url = url.replaceAll('"', '')
  //     }
  //     console.log("cleaned url: ", url)
  //     // 生成替换后的 URL
  //     // const source = prefix + new URL(url).host
  //     // const source2 = prefix + new URL(url)
  //     // const value = this.transformUrl(ctx, source.startsWith('http') ? source : (ctx.meta.scheme + ':' + source))
  //     dict[url] = this.transformUrl2(ctx, url)
  //     console.log("key: ", url, " value: ", dict[url])
  //   })
  //   // 按长度降序排列，优先替换长链接，防止部分替换
  //   Object.entries(dict).sort((a, b) => b[0].length - a[0].length).forEach(ele => {
  //     const [key, value] = ele
  //     console.log("replace ", key, " to ", value)
  //     res.data = res.data.replaceAll(key, value)
  //   })
  //   return res.data
  // }
  transformUrl2 (ctx, url) {
    const { vpnDomain, httpsEnabled, httpVpnDomain, httpsVpnDomain } = this.config
    url = (url ? url.toString() : '').trim()
    if (!url || url.split('?')[0].indexOf('//') < 0) {
      if (ctx.scheme){
        if (url.indexOf('?') < 0){
          return url + "?__webvpn_origin_scheme__=" + ctx.scheme
        }
        else{
          if (url.indexOf("__webvpn_origin_scheme__") < 0){
            return url+ "&__webvpn_origin_scheme__=" + ctx.scheme
          }
          else{
            return url
          }
        }
      }
      else{
        return url
      }
    }
    if (url.indexOf('http') < 0 && url.indexOf('//') > 0) {
      url = url.slice(url.indexOf('//'))
    }
    if (url.startsWith('//')) {
      url = ctx.scheme + url
    }
    if (url.indexOf('http://') > 0 || url.indexOf('https://') > 0) {
      url = url.slice(url.indexOf('http'))
    }
    const u = new URL(url)
    if (httpsEnabled){
        u.host = encodeHost(u.host) + httpsVpnDomain
    }
    else{
        u.host = encodeHost(u.host) + (u.protocol === 'http:' ? httpVpnDomain : httpsVpnDomain)
    }
    u.searchParams.set("__webvpn_origin_scheme__", u.protocol.slice(0, -1))
    u.protocol = 1 ? "https:" : "http:"
    if (u.host.includes(vpnDomain)) {
      // if (url.startsWith('http') && webvpn.protocol === 'http:') {
        // return url.replace('https://', 'http://')
      // }
      return url
    }
    console.log("intercept.js: ", u.toString())
    return u.toString()
  }

  // 转换单个 URL 为 VPN 代理 URL
  transformUrl (ctx, url) {
    const { httpsEnabled, httpVpnDomain, httpsVpnDomain } = this.config
    const u = new URL(url)
    if (httpsEnabled){
        u.host = encodeHost(u.host) + httpsVpnDomain
    }
    else{
        u.host = encodeHost(u.host) + (u.protocol === 'http:' ? httpVpnDomain : httpsVpnDomain)
    }
    u.searchParams.set("__webvpn_origin_scheme__", u.protocol.slice(0, -1))
    u.protocol = httpsEnabled ? "https:": "http:"
    // 将 host 编码后拼接 VPN 域名

    // Warn 原行为：url.replace(u.host, encodeHost(u.host) + vpnDomain)，可能导致部分问题
    console.log("transformUrl: ", u.toString())
    return u.toString()
  }

  // 处理 HTML 特有逻辑，如移除 CSP 限制
  processHtml (ctx, res) {
    const match = res.data.match(/<meta\s+http-equiv=\"Content-Security-Policy\"[^>]+>/)
    if (match) {
      res.data = res.data.replace(match[0], '')
    }
    return res.data
  }

  // 处理 HTML 中的 <script> 标签代码
  processHtmlScopeCodes (ctx, code) {
    // 匹配所有 script 标签内容
    const matches = [...code.matchAll(/<script([^>]*)>([\S\s]*?)<\/script>/gi)].filter(match => {
      const typeIndex = match[1].indexOf('type=')
      let isScript = true
      if (typeIndex > 0) {
        // 判断是否为 JS 脚本 (排除 type="text/template" 等)
        const type = match[1].slice(typeIndex + 6).split(match[1][typeIndex + 5])[0]
        isScript = type.indexOf('javascript') >= 0
        if (
          !isScript
          && type.indexOf('text/') < 0
          && !type.includes('json')
        ) {
          isScript = true
        }
      }
      return isScript && match[2]
    })
    // 从后往前替换，保持索引正确
    matches.sort((a, b) => b.index - a.index)
    matches.forEach(match => {
      const index = match[0].length - match[2].length - 9 + match.index
      // 调用 refactorJsScopeCode 包装代码
      code = code.slice(0, index) + this.refactorJsScopeCode(ctx, match[2]) + code.slice(index + match[2].length)
    })
    return code
  }

  // 处理独立的 JS 文件内容
  processJsScopeCode (ctx, code) {
    // 如果看起来像 JSON，跳过
    if (code[0] === '{' || code[0] === '[') {
      try {
        JSON.parse(code)
        ctx.meta.mime = 'json'
        return code
      } catch {}
    }
    return this.refactorJsScopeCode(ctx, code, true)
  }

  // 核心 JS 包装逻辑：使用 with 和 Proxy 拦截全局变量
  refactorJsScopeCode (ctx, code, isJsFile = false) {
    const { httpsEnabled, site } = this.config
    const { scheme, target } = ctx.meta
    const prefix = site.origin.slice(site.origin.indexOf('//'))
    const siteUrl = (httpsEnabled ? scheme : 'http') + ':' + prefix
    let result = ''
    // 如果是独立 JS 文件，可能在 Worker 中运行，需要注入 Worker 上下文代码
    if (isJsFile) {
      result += this.jsWorkerContextCode.replace('if (!self.window) {', 'if (!self.window) {\n' + this.convertDomainsCode)
        .replace('#targetUrl#', target.href).replace('#siteUrl#', siteUrl)
    }
    // 包裹 with (self.__context_proxy__) { ... }
    result += this.jsScopePrefixCode
            + code
            + '\n}\n'
            + this.calcHoistIdentifiersCode(code) // 处理变量提升
            + this.jsScopeSuffixCode
    return result
  }

  // 处理 var 和 function 的变量提升，确保它们挂载到代理对象上而不是全局
  calcHoistIdentifiersCode (code) {
    const matches = [...code.matchAll(/(function|class)\s+([\$\_\w]+)\s*\(/g)]
    if (!matches.length) return ''
    const names = matches.map(m => m[2]).filter(k => !this.jsKeywords.includes(k))
    return names.map(n => `try { self.${n} = ${n}; } catch {}`).join('\n')
  }

  // 在 HTML 头部注入 WebVPN 的核心客户端脚本
  async appendScript (ctx, res) {
    const {
      httpsEnabled, httpVpnDomain, httpsVpnDomain,
      interceptLog, enablePlugins, debug, disableDevtools
    } = this.config
    const { disableJump = this.config.disableJump, confirmJump = this.config.confirmJump } = ctx.meta
    const { base, scheme, target, isMainSession, shareId, customCode } = ctx.meta
    const { data } = res
    const prefix = '//www' + (httpsEnabled && scheme === 'https' ? httpsVpnDomain : httpVpnDomain)
    const siteUrl = (httpsEnabled ? scheme : 'http') + ':' + prefix
    const pageUrl = this.transformUrl(ctx, target.href)
    // 注入的脚本代码
    const code = `
    <script>
      self.webvpn = {
        siteUrl: '${siteUrl}',
        protocol: '${scheme}:',
        sourceUrl: '${target.href}',
        pageUrl: '${pageUrl}',
        hostname: '${target.hostname}',
        httpVpnDomain: '${httpVpnDomain}',
        httpsVpnDomain: '${httpsVpnDomain}',
        base: '${base}',
        interceptLog: ${interceptLog},
        disableJump: ${disableJump},
        confirmJump: ${confirmJump},
        isMainSession: ${isMainSession},
        shareId: '${shareId}',
      };
      // 注入域名转换代码
      const convertDomainsCode = \`${this.convertDomainsCode}\`
      eval(convertDomainsCode)
      ${customCode || ''}
      // 注入拦截代码
      webvpn.intercept_code = ${JSON.stringify(this.jsInterceptCode.toString())}
      eval(webvpn.intercept_code)
      // 准备好 Worker 的包装代码模板
      webvpn.worker_wrapper_code = convertDomainsCode + \`
        ${this.jsWorkerContextCode.replace('#siteUrl#', siteUrl)}
        ${this.jsScopePrefixCode}
          #CODE#
        }
        ${this.jsScopeSuffixCode}
      \`
    </script>
    ${
      enablePlugins
      ?
      `<script src="${prefix}/public/plugins.js"></script>`
      : ''
    }
    ${
      debug && !disableDevtools
      ? `
        <script src="https://cdnjs.cloudflare.com/ajax/libs/vConsole/3.15.1/vconsole.min.js"></script>
        <script>new VConsole()</script>
      `
      : ''
    }
    ${
      disableDevtools
      ?
      `<script src="${prefix}/public/disable-devtools.js"></script>`
      : ''
    }
    ${
      isMainSession
      ?
      `<script src="${prefix}/public/share-sessions.js"></script>`
      : ''
    }
    ${
      // 如果是共享会话，注入 Cookie 和 LocalStorage
      !isMainSession && shareId
      ?
      `<script>
        const { cookie, localStorage: local } = ${await globalCache.getItem(shareId + '-clientCache') || '{}'}
        document.cookie += cookie
        localStorage.clear()
        for (let key in local) localStorage[key] = local[key]
      </script>`
      : ''
    }
    <script>
      // 移除注入的脚本标签本身，保持 DOM 干净
      const ss = Array.from(document.querySelectorAll('script'));
      ss.forEach(script => script.remove());
    </script>
    `
    const hasDoctype = /^\s*?\<\!DOCTYPE html\>/i.test(res.data)
    // 插入到 DOCTYPE 之后或最前面
    return (hasDoctype ? '<!DOCTYPE html>\n' : '') + code + data
  }

  // 其他杂项处理，如 JSON 序列化、移除 SourceMap
  processOthers (ctx, res) {
    if (ctx.meta.mime === 'json' && typeof res.data === 'string') {
      res.data = JSON.stringify(res.data)
    }
    if (this.config.disableSourceMap) {
      if (ctx.meta.mime === 'html' || ctx.meta.mime === 'js') {
        res.data = res.data.replaceAll('sourceMappingURL', '')
      }
    }
  }

  // 根据 URL 和请求方法判断响应类型
  getResponseType (ctx, url) {
    if (ctx.method === 'PUT' || ctx.method === 'POST') return 'text'
    const index = url.indexOf('?')
    const link = index < 0 ? url : url.slice(0, index)
    // 根据扩展名判断
    for (let reg of this.mimeRegs) {
      if (reg[0].test(link)) {
        return reg[1]
      }
    }
    // 根路径默认为 html
    if (new URL(link).pathname === '/') {
      return 'html'
    }
    return 'text'
  }

  // 获取请求配置（如图片需要 arraybuffer）
  getRequestOptions (ctx) {
    const config = { }
    if (ctx.meta.mime === 'image') {
      config.responseType = 'arraybuffer'
    }
    return config
  }

  // 初始化并重写响应头 (Set-Cookie, Location, CSP, CORS)
  async initResponseHeaders (ctx, res) {
    const { httpsEnabled, vpnDomain, httpVpnDomain, httpsVpnDomain, domainMode, site } = this.config
    const { isMainSession, shareId, scheme, target } = ctx.meta
    let headers = {}
    // 标准化 Header 格式
    if (typeof res.headers.raw === 'function') {
      const raw = res.headers.raw()
      for (let key in raw) {
        headers[key.toLowerCase()] = raw[key]
      }
    } else {
      for (let key in res.headers) {
        const value = res.headers[key]
        headers[key.toLowerCase()] = Array.isArray(value) ? value : [value]
      }
    }
    // 重写 CORS 头
    if (headers['access-control-allow-origin']) {
      headers['access-control-allow-origin'] = headers['access-control-allow-origin'].map(e => {
        if (e === '*') return e
        const host = e.indexOf('http') >= 0 ? new URL(e).host : e
        const vpnDomain = e.indexOf('http://') >= 0 ? httpVpnDomain : httpsVpnDomain
        let domain = encodeHost(host)
        if (shareId) {
          domain += '-' + (isMainSession ? 'main' : 'share') + '-' + shareId
        }
        domain += vpnDomain
        return e.replace(host, domain)
      })
    }
    headers['content-type'] = [headers['content-type']?.[0] || 'text/html']
    // 重写 CSP 头，防止阻止 VPN 注入的脚本
    if (headers['content-security-policy']) {
      headers['content-security-policy'] = headers['content-security-policy'].map(e => {
        if (
          e.includes('-src')
          || e.includes('unsafe-')
          || e.includes('require-trusted-types-for')
        ) return '' // 直接移除严格的 CSP
        if (e.indexOf('frame-ancestors') < 0 || e === `frame-ancestors 'none';`) return e
        const protocol = (httpsEnabled ? scheme : 'http') + '://'
        return e.replace(
          'frame-ancestors',
          'frame-ancestors ' + protocol + site.host.replace('www', '*')
        )
      })
    }
    // 重写 Location 头（302 跳转）
    if (headers['location']) {
      headers['location'] = headers['location'].map(e => {
        if (!e.startsWith('http')) {
          if (e[0] === '/') {
            e = target.origin + e
          }
        }
        return this.transformUrl(ctx, e)
      })
    }
    // 重写 Set-Cookie 的 Domain 属性
    if (headers['set-cookie']) {
      headers['set-cookie'] = headers['set-cookie'].map(e => {
        e = e.replace(' Secure;', '') // 可能会破坏 HTTPS，先移除
        if (!/domain=/i.test(e)) {
          return e + '; domain=' + encodeHost(target.host) + vpnDomain
        }
        return e.split('; ').map(p => {
          if (!/domain=/i.test(p)) return p
          let domain = p.split('=')[1]
          const hasDot = domain[0] === '.'
          if (hasDot) domain = domain.slice(1)
          if (domainMode === 'original') {
            domain = encodeHost(domain) + vpnDomain
            if (hasDot) domain = '.' + domain
          } else {
            // warn warn warn warn warn warn
            // underline 模式不支持 cookie domain
            domain = vpnDomain
          }
          return 'domain=' + domain
        }).join('; ')
      })
    }
    if (!headers['access-control-allow-origin']) {
      headers['access-control-allow-origin'] = ['*']
    }
    // 强制升级 HTTPS
    if (this.config.httpsEnabled && scheme === 'https') {
      if (!headers['content-security-policy']) {
        headers['content-security-policy'] = []
      }
      headers['content-security-policy'].push('upgrade-insecure-requests')
    }
    headers['x-frame-options'] = ['allowall'] // 允许 iframe
    // 注入共享会话的 Cookie
    if (!isMainSession && shareId) {
      const cookie = await globalCache.getItem(shareId + '-cookie')
      if (cookie) headers['set-cookie'] = cookie
    }
    return headers
  }

  // 根据 Content-Type 判断 MIME
  getMimeByResponseHeaders (headers) {
    const contentType = headers['content-type']?.[0] || ''
    const mime = Object.keys(this.mimeDict).find(mime => {
      const parts = this.mimeDict[mime].replaceAll(' ', '').split(',')
      return parts.some(part => {
        return contentType.split(';')[0].indexOf(part) >= 0
      })
    })
    if (!mime && contentType.startsWith('image/')) {
      return 'image'
    }
    return mime
  }

  // 重写请求头中的 Origin/Host/Referer
  setOriginHeaders (ctx, headers) {
    if (headers['host']) {
      headers['host'] = this.convertHost(headers['host'])
    }
    if (headers['origin']) {
      const host = new URL(headers['origin']).host
      headers['origin'] = headers['origin'].replace(host, this.convertHost(host))
    }
    const referer = headers['referer']
    if (referer) {
      const { site, httpVpnDomain, httpsVpnDomain } = this.config
      const vpnDomain = referer.startsWith('http://') ? httpVpnDomain : httpsVpnDomain
      // 防止 Referer 泄露或不正确
      if (referer.indexOf(site.host) < 0 || referer.indexOf(vpnDomain) < 0) {
        delete headers['referer']
      } else {
        const host = new URL(referer).host
        headers['referer'] = referer.replace(host, this.convertHost(host))
      }
    }
  }

  // 将 VPN 域名还原为真实 Host
  convertHost (host) {
    const { httpVpnDomain, httpsVpnDomain } = this.config
    host = host.split('-')[0].replace(httpsVpnDomain, '').replace(httpVpnDomain, '')
    return decodeHost(host)
  }

  // 转换响应数据的字符集 (如 GBK 转 UTF-8) 并解压 (ZSTD)
  async convertCharsetData (ctx, headers, res) {
    if (ctx.meta.mime !== 'html' && ctx.meta.mime !== 'js') {
      return res.text()
    }
    let text, buffer
    // 处理 ZSTD 压缩
    if (res.headers.get('content-encoding') === 'zstd') {
      res.headers.delete('content-encoding')
      text = await new Promise(resolve => {
        let body = ''
        const stream = res.body.pipe(ZSTDDecompress())
        stream.on('data', chunk => body += chunk)
        stream.on('end', () => resolve(body))
      })
    } else {
      buffer = Buffer.from(await res.arrayBuffer())
      text = iconv.decode(buffer, 'utf-8') // 默认先按 UTF-8 解码
    }
    let contentType = headers['content-type']?.[0] || ''
    let charset = contentType.split('charset=')[1]?.toLowerCase()
    // 尝试检测字符集
    if (!charset) {
      let match = text.match(/<meta charset=[\"\'][^"'\/>]+/)
      if (!match) {
        match = text.match(/<meta http-equiv=\"Content-Type\" content=\"text\/html;\s*charset=[^"'\/>]+/i)
      }
      if (!match) {
        return text
      }
      charset = match[0].split('charset=')[1].replaceAll('"', '').toLowerCase()
      contentType = 'text/html; charset=' + charset
    }
    if (charset === 'utf-8' || charset === 'utf8') {
      return text
    }
    // 如果不是 UTF-8，使用 iconv 重新解码
    headers['content-type'] = [contentType.replace(charset, 'utf-8')]
    if (buffer) {
      text = iconv.decode(buffer, charset)
      // 修改 meta 标签为 utf-8
      text = text.replace(/<meta charset="\w+">/, '<meta charset="utf-8">')
    }
    return text
  }

  // 检测是否为 JSONP
  isJsonpResponse (data, ctx) {
    if (ctx.meta.mime === 'html') {
      return /^[\w\$_]+\((\{|\[)/.test(data)
    }
    return false
  }

  // 检测是否为 JSON
  isJsonResponse (data, ctx) {
    if (ctx.meta.mime === 'html') {
      try {
        JSON.parse(data)
        return true
      } catch {
        return false
      }
    }
    return false
  }

  // 删除指定的 Header
  deleteIgnoreHeaders (regexps, headers) {
    const keys = Object.keys(headers)
    for (let key of keys) {
      if (regexps.some(reg => reg.test(key))) {
        delete headers[key]
      }
    }
  }

  // 钩子：是否替换 URL
  shouldReplaceUrls (ctx, res) {
    return true
  }

  // 钩子：请求前
  beforeRequest (ctx, options) { }

  // 钩子：请求后
  afterRequest (ctx, res) { }

  // 自定义响应处理
  customResponse (ctx, res) {
    // 禁用 module 和严格模式，以支持 with 语句进行沙箱隔离
    if (typeof res.data === 'string') {
      res.data = res.data.replaceAll('type="module"', 'type="mod"')
                .replaceAll('type=module', 'type=mod')
                .replaceAll('nomodule', 'nomod')
                .replaceAll(' integrity', ' no-integrity')
                .replaceAll('use strict', '')
                // 替换 with(this) 为安全的写法
                .replace(/[\s\{\}\;]?with\s*\(\s*this\s*\)/g, ' with(this === self ? __self__ : this)')
                // 替换 location 相关操作，使其走代理对象
                // 这个替换并不优雅，也不完整，有问题就取消
                .replace(/location\.(hostname|host|origin|href|protocol|navigate|assign|replace|reload|toString)/g, 'location.__$1__')
    }
  }

  // 钩子：响应前
  beforeResponse (ctx, res) { }
}

export default WebVPN
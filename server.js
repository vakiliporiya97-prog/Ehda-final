/**
 * سامانه‌ی CRM مرکز اهدا پلاسما نوین پلاسما پورا دارو — سرور کامل، تک‌فایلی
 * همه‌چیز (بک‌اند + فرانت‌اند) داخل همین یک فایله؛ فقط با package.json کنارش نیاز داره.
 */
require("dotenv").config();
const path = require("path");
const fs = require("fs");
const https = require("https");
const crypto = require("crypto");
const express = require("express");
const helmet = require("helmet");
const cookieParser = require("cookie-parser");
const rateLimit = require("express-rate-limit");
const bcrypt = require("bcryptjs");
const jwt = require("jsonwebtoken");

/* ============================================================
   بخش ۱: ذخیره‌سازی (فایل JSON ساده)
   ============================================================ */
const DATA_DIR = path.join(__dirname, "data");
const DB_FILE = path.join(DATA_DIR, "db.json");

const DEFAULT_SMS_TEMPLATES = {
  registration: "سلام {name} عزیز، ثبت‌نام شما در {centerName} با موفقیت انجام شد.",
  panelActivated: "{name} عزیز، نتیجه‌ی آزمایش شما تایید شد و پنل شما فعال شد. اکنون می‌توانید نوبت اهدا رزرو کنید.",
  appointmentConfirmed: "{name} عزیز، نوبت شما برای {date} ثبت شد.",
  appointmentReminder: "{name} عزیز، یادآوری می‌کنیم نوبت اهدای شما {date} است.",
  postDonationFollowup: "{name} عزیز، لطفاً وضعیت سلامت خود بعد از اهدا را در پنل ثبت کنید.",
  rebookingEnabled: "{name} عزیز، اکنون می‌توانید نوبت بعدی اهدای خود را رزرو کنید.",
};

function defaultData() {
  return {
    settings: {
      centerName: "مرکز اهدا پلاسما نوین پلاسما پورا دارو",
      minGapHours: 240,
      followUpDays: 1,
      followUpFrequencyPerDay: 1,
      closedWeekdays: [4, 5],
      holidays: [],
      receptionStartHour: "09:00",
      receptionEndHour: "17:00",
      appointmentMode: "auto",
      hourlyCapacity: 4,
      noShowAlertDays: 14,
      smsTemplates: DEFAULT_SMS_TEMPLATES,
    },
    staff: [],
    donors: [],
    notifications: [],
    activityLog: [],
    otps: {},
    nextIds: { staff: 1, donor: 1, appointment: 1, note: 1, reminder: 1, notification: 1, activity: 1 },
  };
}

function ensureDb() {
  if (!fs.existsSync(DATA_DIR)) fs.mkdirSync(DATA_DIR, { recursive: true });
  if (!fs.existsSync(DB_FILE)) fs.writeFileSync(DB_FILE, JSON.stringify(defaultData(), null, 2), "utf8");
}
function readDb() {
  ensureDb();
  const db = JSON.parse(fs.readFileSync(DB_FILE, "utf8"));
  // سازگاری با نسخه‌های قدیمی‌تر دیتابیس در صورت آپدیت برنامه
  if (!db.settings.smsTemplates) db.settings.smsTemplates = DEFAULT_SMS_TEMPLATES;
  if (!db.notifications) db.notifications = [];
  if (!db.activityLog) db.activityLog = [];
  if (!db.otps) db.otps = {};
  if (!db.nextIds.appointment) db.nextIds.appointment = 1;
  if (!db.nextIds.note) db.nextIds.note = 1;
  if (!db.nextIds.reminder) db.nextIds.reminder = 1;
  if (!db.nextIds.notification) db.nextIds.notification = 1;
  if (!db.nextIds.activity) db.nextIds.activity = 1;
  return db;
}
function writeDb(data) {
  const tmp = DB_FILE + ".tmp";
  fs.writeFileSync(tmp, JSON.stringify(data, null, 2), "utf8");
  fs.renameSync(tmp, DB_FILE);
}
function mutate(fn) {
  const db = readDb();
  const result = fn(db);
  writeDb(db);
  return result;
}

/* ============================================================
   بخش ۲: منطق دامنه (اهلیت، نوبت‌دهی، تایم‌لاین، هشدارها)
   ============================================================ */
const STATUS_LABELS = {
  registered: "ثبت‌نام اولیه",
  awaiting_lab: "منتظر جواب آزمایش",
  ready: "آماده تعیین نوبت",
  booked: "نوبت رزرو شده",
  visited: "مراجعه کرد",
  donated: "اهدا انجام شد",
  needs_followup: "نیازمند پیگیری",
  unresponsive: "عدم پاسخگویی",
  inactive: "غیرفعال",
  blocked: "مسدود شده",
};

function isClosedDay(date, s) {
  const iso = new Date(date).toISOString().slice(0, 10);
  if (s.holidays.includes(iso)) return true;
  return s.closedWeekdays.includes(new Date(date).getDay());
}
function nextOpenDate(date, s) {
  const d = new Date(date);
  while (isClosedDay(d, s)) d.setDate(d.getDate() + 1);
  return d;
}

function activeAppointments(donor) {
  return donor.appointments.filter((a) => a.status !== "cancelled");
}
function lastDonationAppointment(donor) {
  return donor.appointments
    .filter((a) => a.donated === true)
    .sort((a, b) => new Date(b.confirmedDate || b.requestedDate) - new Date(a.confirmedDate || a.requestedDate))[0] || null;
}
function currentAppointment(donor) {
  // آخرین نوبتی که هنوز نتیجه‌اش (اهدا/عدم اهدا) ثبت نشده
  return [...donor.appointments]
    .sort((a, b) => new Date(b.createdAt) - new Date(a.createdAt))
    .find((a) => a.status !== "cancelled" && a.donated === null) || null;
}
function effectiveGapHours(donor, settings) {
  return (donor.overrides && donor.overrides.minGapHours) || settings.minGapHours;
}
function nextEligibleDate(donor, settings, now = new Date()) {
  const last = lastDonationAppointment(donor);
  if (!last) return isClosedDay(now, settings) ? nextOpenDate(now, settings) : null;
  const base = new Date(new Date(last.confirmedDate || last.requestedDate).getTime() + effectiveGapHours(donor, settings) * 3600 * 1000);
  return nextOpenDate(base, settings);
}
function isEligibleForBooking(donor, settings, now = new Date()) {
  if (!donor.labApprovedAt) return false;
  if (["blocked", "inactive"].includes(donor.status)) return false;
  if (currentAppointment(donor)) return false; // یک نوبت باز و بی‌نتیجه داره
  const next = nextEligibleDate(donor, settings, now);
  return !next || next <= now;
}

/* ---------- تولید بازه‌های خالی برای حالت خودکار ---------- */
function generateSlotsForDay(dateStr, settings, allDonors) {
  const s = settings;
  const day = new Date(dateStr + "T00:00:00");
  if (isClosedDay(day, s)) return [];
  const [startH, startM] = s.receptionStartHour.split(":").map(Number);
  const [endH, endM] = s.receptionEndHour.split(":").map(Number);
  const slots = [];
  let cursor = new Date(day); cursor.setHours(startH, startM, 0, 0);
  const end = new Date(day); end.setHours(endH, endM, 0, 0);

  // شمارش نوبت‌های موجود در هر ساعت (از بین همه‌ی اهداکنندگان)
  const bookedCount = {};
  allDonors.forEach((d) => {
    d.appointments.forEach((a) => {
      if (a.status === "cancelled") return;
      const dt = new Date(a.confirmedDate || a.requestedDate);
      if (dt.toISOString().slice(0, 10) === dateStr) {
        const key = `${dt.getHours()}:${dt.getMinutes()}`;
        bookedCount[key] = (bookedCount[key] || 0) + 1;
      }
    });
  });

  while (cursor < end) {
    const key = `${cursor.getHours()}:${cursor.getMinutes()}`;
    const used = bookedCount[key] || 0;
    slots.push({ time: cursor.toTimeString().slice(0, 5), capacity: s.hourlyCapacity, used, available: used < s.hourlyCapacity });
    cursor = new Date(cursor.getTime() + 60 * 60 * 1000);
  }
  return slots;
}

/* ---------- پیگیری پس از اهدا ---------- */
function pendingFollowUps(donor, now = new Date()) {
  const appt = donor.appointments.find((a) => a.donated === true && a.followUps && a.followUps.some((f) => !f.completedAt));
  if (!appt) return [];
  const donationDate = new Date(appt.confirmedDate || appt.requestedDate);
  return appt.followUps.filter((f) => {
    if (f.completedAt) return false;
    const due = new Date(donationDate.getTime() + f.dayIndex * 24 * 3600 * 1000);
    return due <= now;
  }).map((f) => ({ ...f, appointmentId: appt.id }));
}

function donorFlagged(donor) {
  return donor.appointments.some((a) => (a.followUps || []).some((f) => f.concerning));
}

/* ---------- تایم‌لاین کامل ---------- */
function buildTimeline(donor, notifications) {
  const events = [];
  events.push({ type: "registered", date: donor.createdAt, label: "ثبت‌نام اولیه" });
  if (donor.survey) events.push({ type: "survey", date: donor.survey.completedAt, label: "تکمیل نظرسنجی اولین مراجعه" });
  if (donor.labApprovedAt) events.push({ type: "lab_approved", date: donor.labApprovedAt, label: "فعال شدن پنل (تایید نتیجه آزمایش)" });
  donor.appointments.forEach((a) => {
    events.push({ type: "appointment_created", date: a.createdAt, label: `درخواست/رزرو نوبت (${a.mode === "auto" ? "خودکار" : "دستی"})` });
    if (a.status === "confirmed") events.push({ type: "appointment_confirmed", date: a.confirmedDate || a.createdAt, label: "تایید نوبت" });
    if (a.status === "cancelled") events.push({ type: "appointment_cancelled", date: a.cancelledAt || a.createdAt, label: "لغو نوبت" });
    if (a.attended === true) events.push({ type: "visited", date: a.visitedAt || a.confirmedDate, label: "مراجعه به مرکز" });
    if (a.donated === true) events.push({ type: "donated", date: a.visitedAt || a.confirmedDate, label: "اهدا انجام شد" });
    if (a.donated === false) events.push({ type: "not_donated", date: a.visitedAt || a.confirmedDate, label: `اهدا انجام نشد (${a.notDonatedReason || "بدون علت"})` });
    (a.followUps || []).forEach((f) => { if (f.completedAt) events.push({ type: "followup", date: f.completedAt, label: `پیگیری روز ${f.dayIndex}` }); });
  });
  (donor.notes || []).forEach((n) => events.push({ type: "note", date: n.createdAt, label: `یادداشت داخلی از ${n.authorUsername}` }));
  (donor.reminders || []).forEach((r) => events.push({ type: "reminder", date: r.createdAt, label: `یادآور ثبت شد: ${r.type}` }));
  notifications.filter((n) => n.donorId === donor.id).forEach((n) => events.push({ type: "sms", date: n.createdAt, label: `پیامک ارسال شد: ${n.templateKey}` }));
  return events.sort((a, b) => new Date(b.date) - new Date(a.date));
}

/* ---------- هشدارهای هوشمند ---------- */
function computeAlerts(db) {
  const now = new Date();
  const alerts = [];
  db.donors.forEach((d) => {
    if (d.status === "ready" && d.labApprovedAt) {
      const days = (now - new Date(d.labApprovedAt)) / 86400000;
      if (days > (db.settings.noShowAlertDays || 14) && !currentAppointment(d)) {
        alerts.push({ type: "no_show", donorId: d.id, donorName: `${d.firstName} ${d.lastName}`, phone: d.phone, detail: `${Math.floor(days)} روز از فعال شدن پنل گذشته و نوبتی نگرفته` });
      }
    }
    const cancelledStreak = [...d.appointments].sort((a, b) => new Date(a.createdAt) - new Date(b.createdAt)).slice(-3);
    if (cancelledStreak.length >= 2 && cancelledStreak.slice(-2).every((a) => a.status === "cancelled")) {
      alerts.push({ type: "consecutive_cancel", donorId: d.id, donorName: `${d.firstName} ${d.lastName}`, phone: d.phone, detail: "چند نوبت متوالی را لغو کرده" });
    }
    if (donorFlagged(d)) {
      alerts.push({ type: "abnormal_symptom", donorId: d.id, donorName: `${d.firstName} ${d.lastName}`, phone: d.phone, detail: "علائم غیرطبیعی در فرم پیگیری ثبت شده" });
    }
    if (d.appointments.some((a) => a.followUps && a.followUps.some((f) => f.callbackRequested))) {
      alerts.push({ type: "callback_requested", donorId: d.id, donorName: `${d.firstName} ${d.lastName}`, phone: d.phone, detail: "درخواست تماس ثبت کرده" });
    }
    if (d.status === "awaiting_lab") {
      alerts.push({ type: "lab_pending", donorId: d.id, donorName: `${d.firstName} ${d.lastName}`, phone: d.phone, detail: "نتیجه‌ی آزمایش هنوز ثبت نشده" });
    }
  });
  return alerts;
}

const domain = {
  STATUS_LABELS, isClosedDay, nextOpenDate, activeAppointments, lastDonationAppointment, currentAppointment,
  nextEligibleDate, isEligibleForBooking, generateSlotsForDay, pendingFollowUps, donorFlagged, buildTimeline, computeAlerts,
};


/* ============================================================
   بخش ۳: احراز هویت (JWT کارکنان + JWT اهداکننده + OTP)
   ============================================================ */
const JWT_SECRET = process.env.JWT_SECRET || "insecure-dev-secret-change-me";

function signStaffToken(staff) {
  return jwt.sign({ id: staff.id, username: staff.username, role: staff.role, kind: "staff" }, JWT_SECRET, { expiresIn: "12h" });
}
function signDonorToken(donor) {
  return jwt.sign({ phone: donor.phone, kind: "donor" }, JWT_SECRET, { expiresIn: "30d" });
}

function requireStaffAuth(req, res, next) {
  const token = req.cookies && req.cookies.staff_token;
  if (!token) return res.status(401).json({ error: "لازمه وارد بشید" });
  try {
    const payload = jwt.verify(token, JWT_SECRET);
    if (payload.kind !== "staff") throw new Error("wrong kind");
    req.staff = payload;
    next();
  } catch (e) { return res.status(401).json({ error: "نشست شما منقضی شده، دوباره وارد بشید" }); }
}
function requireAdmin(req, res, next) {
  if (!req.staff || req.staff.role !== "admin") return res.status(403).json({ error: "فقط مدیر به این بخش دسترسی داره" });
  next();
}
function requireDonorAuth(req, res, next) {
  const token = req.cookies && req.cookies.donor_token;
  if (!token) return res.status(401).json({ error: "لازمه با کد پیامکی وارد بشید" });
  try {
    const payload = jwt.verify(token, JWT_SECRET);
    if (payload.kind !== "donor") throw new Error("wrong kind");
    if (payload.phone !== req.params.phone) return res.status(403).json({ error: "دسترسی غیرمجاز" });
    req.donorPhone = payload.phone;
    next();
  } catch (e) { return res.status(401).json({ error: "نشست شما منقضی شده، دوباره با کد پیامکی وارد بشید" }); }
}

/* ---------- OTP ---------- */
function hashCode(code) { return crypto.createHash("sha256").update(code).digest("hex"); }
function generateOtp(phone) {
  const code = String(Math.floor(100000 + Math.random() * 900000));
  const expiresAt = new Date(Date.now() + 5 * 60 * 1000).toISOString();
  mutate((db) => { db.otps[phone] = { codeHash: hashCode(code), expiresAt }; });
  return code;
}
function verifyOtp(phone, code) {
  const db = readDb();
  const entry = db.otps[phone];
  if (!entry) return false;
  if (new Date(entry.expiresAt) < new Date()) return false;
  const ok = entry.codeHash === hashCode(String(code || ""));
  if (ok) mutate((db2) => { delete db2.otps[phone]; });
  return ok;
}


/* ============================================================
   بخش ۴: پیامک/نوتیفیکیشن و لاگ فعالیت
   ============================================================ */
function renderTemplate(tpl, vars) {
  return tpl.replace(/\{(\w+)\}/g, (m, key) => (vars[key] !== undefined ? vars[key] : m));
}

function httpsPostJson(hostname, pathName, body, headers) {
  return new Promise((resolve) => {
    try {
      const payload = JSON.stringify(body);
      const req = https.request(
        { hostname, path: pathName, method: "POST", headers: { "Content-Type": "application/json", "Content-Length": Buffer.byteLength(payload), ...headers } },
        (res) => {
          let raw = "";
          res.on("data", (c) => (raw += c));
          res.on("end", () => {
            let parsed = null;
            try { parsed = JSON.parse(raw); } catch (e) {}
            resolve({ ok: res.statusCode >= 200 && res.statusCode < 300, status: res.statusCode, data: parsed, raw });
          });
        }
      );
      req.on("error", () => resolve({ ok: false }));
      req.write(payload);
      req.end();
    } catch (e) { resolve({ ok: false }); }
  });
}

/** ارسال واقعی از طریق sms.ir (متد Bulk — ارسال متن آزاد از خط اختصاصی) */
async function sendViaSmsIr(phone, text) {
  const apiKey = process.env.SMS_IR_API_KEY;
  const lineNumber = process.env.SMS_IR_LINE_NUMBER;
  if (!apiKey || !lineNumber) return null; // پیکربندی نشده
  const res = await httpsPostJson(
    "api.sms.ir",
    "/v1/send/bulk",
    { lineNumber: Number(lineNumber), messageText: text, mobiles: [phone], sendDateTime: null },
    { "x-api-key": apiKey }
  );
  const success = res.ok && res.data && Number(res.data.status) === 1;
  return { delivered: success, provider: "sms.ir", raw: res.data || res.raw };
}

/** جایگزین عمومی: اگه به‌جای sms.ir از یک وب‌هوک دیگه استفاده می‌کنید */
async function sendViaGenericWebhook(phone, text) {
  const url = process.env.SMS_WEBHOOK_URL;
  if (!url) return null;
  try {
    const u = new URL(url);
    const res = await httpsPostJson(u.hostname, u.pathname + u.search, { phone, text }, {});
    return { delivered: res.ok, provider: "webhook", raw: res.data || res.raw };
  } catch (e) { return { delivered: false, provider: "webhook" }; }
}

/** ارسال/ثبت یک نوتیفیکیشن برای یک اهداکننده بر اساس یکی از قالب‌های پیامک */
async function notify(db, donor, templateKey, extraVars = {}) {
  const tpl = db.settings.smsTemplates[templateKey] || "";
  const text = renderTemplate(tpl, { name: `${donor.firstName} ${donor.lastName}`, centerName: db.settings.centerName, ...extraVars });

  let delivered = false;
  let provider = "none";
  const viaSmsIr = await sendViaSmsIr(donor.phone, text);
  if (viaSmsIr) { delivered = viaSmsIr.delivered; provider = viaSmsIr.provider; }
  else {
    const viaWebhook = await sendViaGenericWebhook(donor.phone, text);
    if (viaWebhook) { delivered = viaWebhook.delivered; provider = viaWebhook.provider; }
  }

  mutate((d2) => {
    d2.notifications.push({
      id: d2.nextIds.notification++,
      donorId: donor.id,
      templateKey,
      text,
      provider,
      createdAt: new Date().toISOString(),
      delivered,
    });
  });

  return { text, delivered, provider };
}

function logActivity(db, actorUsername, action, detail) {
  mutate((d2) => {
    d2.activityLog.push({ id: d2.nextIds.activity++, actorUsername, action, detail, createdAt: new Date().toISOString() });
  });
}

/** ارسال خام یک پیامک بدون وابستگی به رکورد اهداکننده (مثل کد OTP قبل از ثبت‌نام) */
async function sendRawSms(phone, text) {
  const viaSmsIr = await sendViaSmsIr(phone, text);
  if (viaSmsIr) return viaSmsIr;
  const viaWebhook = await sendViaGenericWebhook(phone, text);
  if (viaWebhook) return viaWebhook;
  return { delivered: false, provider: "none" };
}


/* ============================================================
   بخش ۵: اپ Express و میان‌افزار امنیتی
   ============================================================ */
const app = express();
const PORT = process.env.PORT || 3000;
const isProd = process.env.NODE_ENV === "production";

app.set("trust proxy", 1);
app.use(helmet({
  contentSecurityPolicy: {
    directives: {
      defaultSrc: ["'self'"],
      styleSrc: ["'self'", "'unsafe-inline'", "https://cdn.tailwindcss.com", "https://fonts.googleapis.com"],
      scriptSrc: ["'self'", "'unsafe-inline'", "https://cdn.tailwindcss.com", "https://unpkg.com"],
      fontSrc: ["'self'", "https://fonts.gstatic.com"],
      imgSrc: ["'self'", "data:"],
      connectSrc: ["'self'"],
    },
  },
}));
app.use(express.json({ limit: "300kb" }));
app.use(cookieParser());

const staffCookieOpts = { httpOnly: true, sameSite: "lax", secure: isProd, maxAge: 12 * 60 * 60 * 1000 };
const donorCookieOpts = { httpOnly: true, sameSite: "lax", secure: isProd, maxAge: 30 * 24 * 60 * 60 * 1000 };

const loginLimiter = rateLimit({ windowMs: 15 * 60 * 1000, max: 30 });
app.use("/api/staff-auth/login", loginLimiter);
const otpLimiter = rateLimit({ windowMs: 15 * 60 * 1000, max: 10 });
app.use("/api/donor-auth/request-otp", otpLimiter);
const publicLimiter = rateLimit({ windowMs: 15 * 60 * 1000, max: 400 });
app.use("/api/donor-auth", publicLimiter);
app.use("/api/donors", publicLimiter);

/* ============================================================
   بخش ۶: مسیرهای احراز هویت کارکنان
   ============================================================ */
const staffAuthRouter = express.Router();

staffAuthRouter.post("/login", (req, res) => {
  const { username, password } = req.body || {};
  if (!username || !password) return res.status(400).json({ error: "نام کاربری و رمز عبور لازمه" });
  const db = readDb();
  const staff = db.staff.find((s) => s.username === username);
  if (!staff || !bcrypt.compareSync(password, staff.passwordHash)) return res.status(401).json({ error: "نام کاربری یا رمز عبور اشتباهه" });
  if (staff.blocked) return res.status(403).json({ error: "این حساب مسدود شده" });
  res.cookie("staff_token", signStaffToken(staff), staffCookieOpts);
  logActivity(db, staff.username, "login", "ورود به پنل کارکنان");
  res.json({ id: staff.id, username: staff.username, role: staff.role, mustChangePassword: !!staff.mustChangePassword });
});

staffAuthRouter.post("/logout", requireStaffAuth, (req, res) => {
  res.clearCookie("staff_token");
  logActivity(readDb(), req.staff.username, "logout", "خروج از پنل کارکنان");
  res.json({ ok: true });
});

staffAuthRouter.get("/me", requireStaffAuth, (req, res) => {
  const db = readDb();
  const staff = db.staff.find((s) => s.id === req.staff.id);
  if (!staff) return res.status(401).json({ error: "کاربر یافت نشد" });
  res.json({ id: staff.id, username: staff.username, role: staff.role, mustChangePassword: !!staff.mustChangePassword });
});

staffAuthRouter.post("/change-password", requireStaffAuth, (req, res) => {
  const { currentPassword, newPassword } = req.body || {};
  if (!newPassword || newPassword.length < 6) return res.status(400).json({ error: "رمز جدید باید حداقل ۶ کاراکتر باشه" });
  const result = mutate((db) => {
    const staff = db.staff.find((s) => s.id === req.staff.id);
    if (!staff) return { error: "کاربر یافت نشد" };
    if (!bcrypt.compareSync(currentPassword || "", staff.passwordHash)) return { error: "رمز فعلی اشتباهه" };
    staff.passwordHash = bcrypt.hashSync(newPassword, 12);
    staff.mustChangePassword = false;
    return { ok: true };
  });
  if (result.error) return res.status(400).json(result);
  res.json(result);
});

app.use("/api/staff-auth", staffAuthRouter);

/* ============================================================
   بخش ۷: مسیرهای احراز هویت اهداکننده (OTP)
   ============================================================ */
const donorAuthRouter = express.Router();

function normalizePhone(p) { return String(p || "").replace(/[^0-9]/g, ""); }

donorAuthRouter.post("/request-otp", async (req, res) => {
  const phone = normalizePhone(req.body && req.body.phone);
  if (phone.length < 10) return res.status(400).json({ error: "شماره موبایل معتبر نیست" });
  const code = generateOtp(phone);
  const result = await sendRawSms(phone, `کد ورود شما: ${code}`);
  // اگه سرویس پیامک وصل نشده یا ارسال ناموفق بود، کد رو مستقیم برمی‌گردونیم تا بشه تست کرد (حالت دمو)
  res.json({ ok: true, demoCode: result.delivered ? undefined : code });
});

donorAuthRouter.post("/verify-otp", (req, res) => {
  const phone = normalizePhone(req.body && req.body.phone);
  const code = req.body && req.body.code;
  if (!verifyOtp(phone, code)) return res.status(400).json({ error: "کد وارد شده صحیح نیست یا منقضی شده" });
  const db = readDb();
  const donor = db.donors.find((d) => d.phone === phone);
  res.cookie("donor_token", signDonorToken({ phone }), donorCookieOpts);
  res.json({ ok: true, exists: !!donor });
});

donorAuthRouter.post("/register", async (req, res) => {
  const phone = normalizePhone(req.body && req.body.phone);
  const firstName = String((req.body && req.body.firstName) || "").trim();
  const lastName = String((req.body && req.body.lastName) || "").trim();
  const age = Number(req.body && req.body.age);
  if (phone.length < 10) return res.status(400).json({ error: "شماره موبایل معتبر نیست" });
  if (firstName.length < 2 || lastName.length < 2) return res.status(400).json({ error: "نام و نام‌خانوادگی معتبر نیست" });
  if (!age || age < 17 || age > 75) return res.status(400).json({ error: "سن معتبر نیست" });

  const result = mutate((db) => {
    if (db.donors.find((d) => d.phone === phone)) return { error: "این شماره قبلاً ثبت شده" };
    const donor = {
      id: db.nextIds.donor++, firstName, lastName, phone, age, status: "registered",
      survey: null, labApprovedAt: null, appointments: [], notes: [], reminders: [],
      overrides: {}, createdAt: new Date().toISOString(),
    };
    db.donors.push(donor);
    return { donor };
  });
  if (result.error) return res.status(409).json(result);

  res.cookie("donor_token", signDonorToken({ phone }), donorCookieOpts);
  const db = readDb();
  await notify(db, result.donor, "registration");
  logActivity(db, "system", "donor_registered", `اهداکننده‌ی جدید: ${firstName} ${lastName} (${phone})`);
  res.status(201).json({ ok: true });
});

app.use("/api/donor-auth", donorAuthRouter);

/* ============================================================
   بخش ۸: مسیرهای خودخدمتی اهداکننده
   ============================================================ */
const donorSelfRouter = express.Router();
donorSelfRouter.use("/:phone", requireDonorAuth);

function donorView(d, db) {
  const now = new Date();
  return {
    ...d,
    statusLabel: domain.STATUS_LABELS[d.status] || d.status,
    eligibleForBooking: domain.isEligibleForBooking(d, db.settings, now),
    nextEligibleDate: domain.nextEligibleDate(d, db.settings, now),
    currentAppointment: domain.currentAppointment(d),
    pendingFollowUps: domain.pendingFollowUps(d, now),
    notes: undefined, // یادداشت‌های داخلی هرگز برای خود اهداکننده ارسال نمی‌شه
  };
}

donorSelfRouter.get("/:phone", (req, res) => {
  const db = readDb();
  const donor = db.donors.find((d) => d.phone === req.params.phone);
  if (!donor) return res.status(404).json({ error: "پرونده پیدا نشد" });
  res.json(donorView(donor, db));
});

donorSelfRouter.get("/:phone/notifications", (req, res) => {
  const db = readDb();
  const donor = db.donors.find((d) => d.phone === req.params.phone);
  if (!donor) return res.status(404).json({ error: "پرونده پیدا نشد" });
  res.json(db.notifications.filter((n) => n.donorId === donor.id).sort((a, b) => new Date(b.createdAt) - new Date(a.createdAt)));
});

donorSelfRouter.post("/:phone/survey", (req, res) => {
  const result = mutate((db) => {
    const donor = db.donors.find((d) => d.phone === req.params.phone);
    if (!donor) return { error: "پرونده پیدا نشد" };
    if (donor.survey) return { error: "نظرسنجی اولین مراجعه قبلاً ثبت شده" };
    donor.survey = { ...req.body, completedAt: new Date().toISOString() };
    donor.status = "awaiting_lab";
    return { donor };
  });
  if (result.error) return res.status(400).json(result);
  const db = readDb();
  res.json(donorView(result.donor, db));
});

donorSelfRouter.get("/:phone/slots", (req, res) => {
  const date = req.query.date; // YYYY-MM-DD
  if (!date) return res.status(400).json({ error: "تاریخ لازمه" });
  const db = readDb();
  res.json(domain.generateSlotsForDay(date, db.settings, db.donors));
});

donorSelfRouter.post("/:phone/appointments", (req, res) => {
  const { date, time, note } = req.body || {}; // date: YYYY-MM-DD, time: HH:MM (فقط برای حالت خودکار الزامیه)
  const result = mutate((db) => {
    const donor = db.donors.find((d) => d.phone === req.params.phone);
    if (!donor) return { error: "پرونده پیدا نشد" };
    if (!domain.isEligibleForBooking(donor, db.settings)) return { error: "در حال حاضر امکان رزرو نوبت ندارید" };
    if (!date) return { error: "تاریخ لازمه" };

    let appt;
    if (db.settings.appointmentMode === "auto") {
      if (!time) return { error: "ساعت لازمه" };
      const slots = domain.generateSlotsForDay(date, db.settings, db.donors);
      const slot = slots.find((s) => s.time === time);
      if (!slot || !slot.available) return { error: "این بازه‌ی زمانی دیگه ظرفیت نداره" };
      const confirmedDate = new Date(`${date}T${time}:00`).toISOString();
      appt = { id: db.nextIds.appointment++, mode: "auto", requestedDate: confirmedDate, confirmedDate, status: "confirmed",
        attended: null, donated: null, notDonatedReason: null, followUps: [], createdAt: new Date().toISOString(), note: note || "" };
    } else {
      const requestedDate = new Date(`${date}T${time || "09:00"}:00`).toISOString();
      appt = { id: db.nextIds.appointment++, mode: "manual", requestedDate, confirmedDate: null, status: "requested",
        attended: null, donated: null, notDonatedReason: null, followUps: [], createdAt: new Date().toISOString(), note: note || "" };
    }
    donor.appointments.push(appt);
    donor.status = "booked";
    return { donor, appt };
  });
  if (result.error) return res.status(400).json(result);
  const db = readDb();
  if (result.appt.status === "confirmed") notify(db, result.donor, "appointmentConfirmed", { date: result.appt.confirmedDate });
  res.status(201).json(donorView(result.donor, db));
});

donorSelfRouter.post("/:phone/appointments/:id/cancel", (req, res) => {
  const id = Number(req.params.id);
  const result = mutate((db) => {
    const donor = db.donors.find((d) => d.phone === req.params.phone);
    if (!donor) return { error: "پرونده پیدا نشد" };
    const appt = donor.appointments.find((a) => a.id === id);
    if (!appt) return { error: "نوبت پیدا نشد" };
    appt.status = "cancelled";
    appt.cancelledAt = new Date().toISOString();
    appt.cancelledBy = "donor";
    if (donor.status === "booked") donor.status = "ready";
    return { donor };
  });
  if (result.error) return res.status(400).json(result);
  res.json(donorView(result.donor, readDb()));
});

donorSelfRouter.post("/:phone/appointments/:id/accept-reschedule", (req, res) => {
  const id = Number(req.params.id);
  const result = mutate((db) => {
    const donor = db.donors.find((d) => d.phone === req.params.phone);
    if (!donor) return { error: "پرونده پیدا نشد" };
    const appt = donor.appointments.find((a) => a.id === id);
    if (!appt || appt.status !== "rescheduled_by_admin") return { error: "درخواستی برای تایید پیدا نشد" };
    appt.status = "confirmed";
    return { donor };
  });
  if (result.error) return res.status(400).json(result);
  res.json(donorView(result.donor, readDb()));
});

donorSelfRouter.post("/:phone/followups/:appointmentId/:dayIndex", (req, res) => {
  const appointmentId = Number(req.params.appointmentId);
  const dayIndex = Number(req.params.dayIndex);
  const { generalCondition, dizziness, injectionSiteIssue, satisfied, readyForNext, callbackRequested, notes } = req.body || {};
  const concerning = !!dizziness || !!injectionSiteIssue || satisfied === false;
  const result = mutate((db) => {
    const donor = db.donors.find((d) => d.phone === req.params.phone);
    if (!donor) return { error: "پرونده پیدا نشد" };
    const appt = donor.appointments.find((a) => a.id === appointmentId);
    if (!appt) return { error: "نوبت پیدا نشد" };
    let f = (appt.followUps || []).find((x) => x.dayIndex === dayIndex);
    if (!f) return { error: "این پیگیری هنوز فعال نشده" };
    Object.assign(f, { generalCondition, dizziness: !!dizziness, injectionSiteIssue: !!injectionSiteIssue, satisfied: !!satisfied, readyForNext: !!readyForNext, callbackRequested: !!callbackRequested, notes: notes || "", concerning, completedAt: new Date().toISOString() });
    if (concerning) donor.status = "needs_followup";
    return { donor };
  });
  if (result.error) return res.status(400).json(result);
  res.json(donorView(result.donor, readDb()));
});

app.use("/api/donors", donorSelfRouter);

/* ============================================================
   بخش ۹: مسیرهای مدیریت/CRM
   ============================================================ */
const adminRouter2 = express.Router();
adminRouter2.use(requireStaffAuth);

function donorAdminView(d, db) {
  const now = new Date();
  return {
    ...d,
    statusLabel: domain.STATUS_LABELS[d.status] || d.status,
    eligibleForBooking: domain.isEligibleForBooking(d, db.settings, now),
    nextEligibleDate: domain.nextEligibleDate(d, db.settings, now),
    currentAppointment: domain.currentAppointment(d),
    pendingFollowUps: domain.pendingFollowUps(d, now),
    flagged: domain.donorFlagged(d),
    timeline: domain.buildTimeline(d, db.notifications),
  };
}

/* ============================================================
   اهداکنندگان و CRM
   ============================================================ */
adminRouter2.get("/donors", (req, res) => {
  const db = readDb();
  const { q } = req.query;
  let donors = db.donors;
  if (q) {
    const needle = q.trim().toLowerCase();
    donors = donors.filter((d) =>
      `${d.firstName} ${d.lastName}`.toLowerCase().includes(needle) || d.phone.includes(needle)
    );
  }
  res.json(donors.map((d) => donorAdminView(d, db)));
});

adminRouter2.get("/donors/:phone", (req, res) => {
  const db = readDb();
  const donor = db.donors.find((d) => d.phone === req.params.phone);
  if (!donor) return res.status(404).json({ error: "پیدا نشد" });
  res.json(donorAdminView(donor, db));
});

adminRouter2.put("/donors/:phone/status", (req, res) => {
  const { status } = req.body || {};
  if (!domain.STATUS_LABELS[status]) return res.status(400).json({ error: "وضعیت نامعتبره" });
  const result = mutate((db) => {
    const donor = db.donors.find((d) => d.phone === req.params.phone);
    if (!donor) return { error: "پیدا نشد" };
    donor.status = status;
    return { donor };
  });
  if (result.error) return res.status(404).json(result);
  logActivity(readDb(), req.staff.username, "status_change", `وضعیت ${req.params.phone} به «${domain.STATUS_LABELS[status]}» تغییر کرد`);
  res.json(donorAdminView(result.donor, readDb()));
});

adminRouter2.post("/donors/:phone/approve-lab", async (req, res) => {
  const result = mutate((db) => {
    const donor = db.donors.find((d) => d.phone === req.params.phone);
    if (!donor) return { error: "پیدا نشد" };
    donor.labApprovedAt = new Date().toISOString();
    donor.status = "ready";
    return { donor };
  });
  if (result.error) return res.status(404).json(result);
  const db = readDb();
  await notify(db, result.donor, "panelActivated");
  logActivity(db, req.staff.username, "lab_approved", `نتیجه‌ی آزمایش ${req.params.phone} تایید شد`);
  res.json(donorAdminView(result.donor, readDb()));
});

adminRouter2.delete("/donors/:phone", requireAdmin, (req, res) => {
  const result = mutate((db) => {
    const before = db.donors.length;
    db.donors = db.donors.filter((d) => d.phone !== req.params.phone);
    if (db.donors.length === before) return { error: "پیدا نشد" };
    return { ok: true };
  });
  if (result.error) return res.status(404).json(result);
  logActivity(readDb(), req.staff.username, "donor_deleted", `اهداکننده‌ی ${req.params.phone} حذف شد`);
  res.json(result);
});

adminRouter2.post("/donors/:phone/block", (req, res) => {
  const result = mutate((db) => {
    const donor = db.donors.find((d) => d.phone === req.params.phone);
    if (!donor) return { error: "پیدا نشد" };
    donor.status = "blocked";
    return { donor };
  });
  if (result.error) return res.status(404).json(result);
  logActivity(readDb(), req.staff.username, "donor_blocked", `اهداکننده‌ی ${req.params.phone} مسدود شد`);
  res.json(donorAdminView(result.donor, readDb()));
});

adminRouter2.post("/donors/:phone/unblock", (req, res) => {
  const result = mutate((db) => {
    const donor = db.donors.find((d) => d.phone === req.params.phone);
    if (!donor) return { error: "پیدا نشد" };
    donor.status = donor.labApprovedAt ? "ready" : donor.survey ? "awaiting_lab" : "registered";
    return { donor };
  });
  if (result.error) return res.status(404).json(result);
  logActivity(readDb(), req.staff.username, "donor_unblocked", `اهداکننده‌ی ${req.params.phone} رفع مسدودی شد`);
  res.json(donorAdminView(result.donor, readDb()));
});

adminRouter2.delete("/donors/:phone/survey", requireAdmin, (req, res) => {
  const result = mutate((db) => {
    const donor = db.donors.find((d) => d.phone === req.params.phone);
    if (!donor) return { error: "پیدا نشد" };
    donor.survey = null;
    if (donor.status === "awaiting_lab") donor.status = "registered";
    return { donor };
  });
  if (result.error) return res.status(404).json(result);
  logActivity(readDb(), req.staff.username, "survey_deleted", `نظرسنجی ${req.params.phone} حذف شد`);
  res.json(donorAdminView(result.donor, readDb()));
});

/* ---------- یادداشت‌های داخلی CRM ---------- */
adminRouter2.post("/donors/:phone/notes", (req, res) => {
  const { body } = req.body || {};
  if (!body || !body.trim()) return res.status(400).json({ error: "متن یادداشت خالیه" });
  const result = mutate((db) => {
    const donor = db.donors.find((d) => d.phone === req.params.phone);
    if (!donor) return { error: "پیدا نشد" };
    donor.notes.push({ id: db.nextIds.note++, authorUsername: req.staff.username, body: body.trim(), createdAt: new Date().toISOString() });
    return { donor };
  });
  if (result.error) return res.status(404).json(result);
  res.status(201).json(donorAdminView(result.donor, readDb()));
});

adminRouter2.delete("/donors/:phone/notes/:noteId", requireAdmin, (req, res) => {
  const noteId = Number(req.params.noteId);
  const result = mutate((db) => {
    const donor = db.donors.find((d) => d.phone === req.params.phone);
    if (!donor) return { error: "پیدا نشد" };
    donor.notes = donor.notes.filter((n) => n.id !== noteId);
    return { donor };
  });
  if (result.error) return res.status(404).json(result);
  res.json(donorAdminView(result.donor, readDb()));
});

/* ---------- یادآورهای پیگیری ---------- */
adminRouter2.post("/donors/:phone/reminders", (req, res) => {
  const { type, dueDate, note } = req.body || {};
  if (!type || !dueDate) return res.status(400).json({ error: "نوع و تاریخ یادآور لازمه" });
  const result = mutate((db) => {
    const donor = db.donors.find((d) => d.phone === req.params.phone);
    if (!donor) return { error: "پیدا نشد" };
    donor.reminders.push({ id: db.nextIds.reminder++, type, dueDate, note: note || "", done: false, createdByUsername: req.staff.username, createdAt: new Date().toISOString() });
    return { donor };
  });
  if (result.error) return res.status(404).json(result);
  res.status(201).json(donorAdminView(result.donor, readDb()));
});

adminRouter2.post("/donors/:phone/reminders/:id/done", (req, res) => {
  const id = Number(req.params.id);
  const result = mutate((db) => {
    const donor = db.donors.find((d) => d.phone === req.params.phone);
    if (!donor) return { error: "پیدا نشد" };
    const r = donor.reminders.find((x) => x.id === id);
    if (!r) return { error: "یادآور پیدا نشد" };
    r.done = true;
    return { donor };
  });
  if (result.error) return res.status(404).json(result);
  res.json(donorAdminView(result.donor, readDb()));
});

adminRouter2.get("/reminders/due", (req, res) => {
  const db = readDb();
  const now = new Date();
  const due = [];
  db.donors.forEach((d) => {
    d.reminders.forEach((r) => {
      if (!r.done && new Date(r.dueDate) <= now) due.push({ ...r, donorId: d.id, donorName: `${d.firstName} ${d.lastName}`, donorPhone: d.phone });
    });
  });
  res.json(due.sort((a, b) => new Date(a.dueDate) - new Date(b.dueDate)));
});

/* ============================================================
   نوبت‌دهی
   ============================================================ */
adminRouter2.get("/appointments/slots", (req, res) => {
  const date = req.query.date;
  if (!date) return res.status(400).json({ error: "تاریخ لازمه" });
  const db = readDb();
  res.json(domain.generateSlotsForDay(date, db.settings, db.donors));
});

adminRouter2.get("/appointments", (req, res) => {
  const db = readDb();
  const list = [];
  db.donors.forEach((d) => d.appointments.forEach((a) => {
    if (a.status !== "cancelled") list.push({ ...a, donorId: d.id, donorName: `${d.firstName} ${d.lastName}`, donorPhone: d.phone });
  }));
  list.sort((a, b) => new Date(a.confirmedDate || a.requestedDate) - new Date(b.confirmedDate || b.requestedDate));
  res.json(list);
});

adminRouter2.post("/donors/:phone/appointments", async (req, res) => {
  const { date, time } = req.body || {};
  if (!date) return res.status(400).json({ error: "تاریخ لازمه" });
  const result = mutate((db) => {
    const donor = db.donors.find((d) => d.phone === req.params.phone);
    if (!donor) return { error: "پیدا نشد" };
    const confirmedDate = new Date(`${date}T${time || "09:00"}:00`).toISOString();
    const appt = { id: db.nextIds.appointment++, mode: "manual", requestedDate: confirmedDate, confirmedDate, status: "confirmed",
      attended: null, donated: null, notDonatedReason: null, followUps: [], createdAt: new Date().toISOString(), note: "ثبت‌شده توسط کارمند" };
    donor.appointments.push(appt);
    donor.status = "booked";
    return { donor, appt };
  });
  if (result.error) return res.status(404).json(result);
  const db = readDb();
  await notify(db, result.donor, "appointmentConfirmed", { date: result.appt.confirmedDate });
  res.status(201).json(donorAdminView(result.donor, readDb()));
});

adminRouter2.post("/donors/:phone/appointments/:id/confirm", async (req, res) => {
  const id = Number(req.params.id);
  const { date } = req.body || {};
  const result = mutate((db) => {
    const donor = db.donors.find((d) => d.phone === req.params.phone);
    if (!donor) return { error: "پیدا نشد" };
    const appt = donor.appointments.find((a) => a.id === id);
    if (!appt) return { error: "نوبت پیدا نشد" };
    appt.confirmedDate = date ? new Date(date).toISOString() : appt.requestedDate;
    appt.status = "confirmed";
    return { donor, appt };
  });
  if (result.error) return res.status(404).json(result);
  const db = readDb();
  await notify(db, result.donor, "appointmentConfirmed", { date: result.appt.confirmedDate });
  res.json(donorAdminView(result.donor, readDb()));
});

adminRouter2.post("/donors/:phone/appointments/:id/propose", (req, res) => {
  const id = Number(req.params.id);
  const { date, note } = req.body || {};
  if (!date) return res.status(400).json({ error: "تاریخ پیشنهادی لازمه" });
  const result = mutate((db) => {
    const donor = db.donors.find((d) => d.phone === req.params.phone);
    if (!donor) return { error: "پیدا نشد" };
    const appt = donor.appointments.find((a) => a.id === id);
    if (!appt) return { error: "نوبت پیدا نشد" };
    appt.confirmedDate = new Date(date).toISOString();
    appt.status = "rescheduled_by_admin";
    appt.adminNote = note || "";
    return { donor };
  });
  if (result.error) return res.status(404).json(result);
  res.json(donorAdminView(result.donor, readDb()));
});

adminRouter2.post("/donors/:phone/appointments/:id/cancel", (req, res) => {
  const id = Number(req.params.id);
  const { reason } = req.body || {};
  const result = mutate((db) => {
    const donor = db.donors.find((d) => d.phone === req.params.phone);
    if (!donor) return { error: "پیدا نشد" };
    const appt = donor.appointments.find((a) => a.id === id);
    if (!appt) return { error: "نوبت پیدا نشد" };
    appt.status = "cancelled";
    appt.cancelledAt = new Date().toISOString();
    appt.cancelledBy = "admin";
    appt.cancelReason = reason || "";
    if (donor.status === "booked") donor.status = "ready";
    return { donor };
  });
  if (result.error) return res.status(404).json(result);
  res.json(donorAdminView(result.donor, readDb()));
});

/** ثبت نتیجه‌ی مراجعه: مراجعه کرد / اهدا انجام شد / اهدا انجام نشد */
adminRouter2.post("/donors/:phone/appointments/:id/outcome", async (req, res) => {
  const id = Number(req.params.id);
  const { attended, donated, notDonatedReason } = req.body || {};
  const result = mutate((db) => {
    const donor = db.donors.find((d) => d.phone === req.params.phone);
    if (!donor) return { error: "پیدا نشد" };
    const appt = donor.appointments.find((a) => a.id === id);
    if (!appt) return { error: "نوبت پیدا نشد" };
    appt.attended = !!attended;
    appt.donated = donated === true ? true : donated === false ? false : null;
    appt.notDonatedReason = notDonatedReason || null;
    appt.visitedAt = new Date().toISOString();
    appt.status = "completed";
    if (appt.donated === true) {
      const days = db.settings.followUpDays || 1;
      appt.followUps = Array.from({ length: days }, (_, i) => ({ dayIndex: i + 1, completedAt: null }));
      donor.status = "donated";
    } else {
      donor.status = "ready";
    }
    return { donor, appt };
  });
  if (result.error) return res.status(404).json(result);
  const db = readDb();
  if (result.appt.donated === true) await notify(db, result.donor, "postDonationFollowup");
  res.json(donorAdminView(result.donor, readDb()));
});

/* ============================================================
   تنظیمات مرکز
   ============================================================ */
adminRouter2.get("/settings", (req, res) => res.json(readDb().settings));

adminRouter2.put("/settings", requireAdmin, (req, res) => {
  const body = req.body || {};
  const allowed = ["centerName", "minGapHours", "followUpDays", "followUpFrequencyPerDay", "closedWeekdays", "holidays", "receptionStartHour", "receptionEndHour", "appointmentMode", "hourlyCapacity", "noShowAlertDays"];
  const result = mutate((db) => {
    allowed.forEach((k) => { if (body[k] !== undefined) db.settings[k] = body[k]; });
    return db.settings;
  });
  logActivity(readDb(), req.staff.username, "settings_updated", "تنظیمات مرکز ویرایش شد");
  res.json(result);
});

adminRouter2.put("/settings/sms-templates", requireAdmin, (req, res) => {
  const result = mutate((db) => {
    db.settings.smsTemplates = { ...db.settings.smsTemplates, ...(req.body || {}) };
    return db.settings.smsTemplates;
  });
  res.json(result);
});

/* ============================================================
   کارکنان
   ============================================================ */
adminRouter2.get("/staff", requireAdmin, (req, res) => {
  res.json(readDb().staff.map((s) => ({ id: s.id, username: s.username, role: s.role, blocked: !!s.blocked, createdAt: s.createdAt })));
});

adminRouter2.post("/staff", requireAdmin, (req, res) => {
  const { username, password, role } = req.body || {};
  if (!username || !password || password.length < 6) return res.status(400).json({ error: "نام کاربری لازمه و رمز باید حداقل ۶ کاراکتر باشه" });
  const result = mutate((db) => {
    if (db.staff.find((s) => s.username === username)) return { error: "این نام کاربری قبلاً وجود داره" };
    const staff = { id: db.nextIds.staff++, username, passwordHash: bcrypt.hashSync(password, 12), role: role === "admin" ? "admin" : "staff", mustChangePassword: true, blocked: false, createdAt: new Date().toISOString() };
    db.staff.push(staff);
    return { staff };
  });
  if (result.error) return res.status(409).json(result);
  res.status(201).json({ id: result.staff.id, username: result.staff.username, role: result.staff.role });
});

adminRouter2.put("/staff/:id/block", requireAdmin, (req, res) => {
  const id = Number(req.params.id);
  const { blocked } = req.body || {};
  const result = mutate((db) => {
    const s = db.staff.find((x) => x.id === id);
    if (!s) return { error: "پیدا نشد" };
    s.blocked = !!blocked;
    return { ok: true };
  });
  if (result.error) return res.status(404).json(result);
  res.json(result);
});

adminRouter2.delete("/staff/:id", requireAdmin, (req, res) => {
  const id = Number(req.params.id);
  if (id === req.staff.id) return res.status(400).json({ error: "نمی‌تونید حساب خودتون رو حذف کنید" });
  const result = mutate((db) => {
    const before = db.staff.length;
    db.staff = db.staff.filter((s) => s.id !== id);
    if (db.staff.length === before) return { error: "پیدا نشد" };
    return { ok: true };
  });
  if (result.error) return res.status(404).json(result);
  res.json(result);
});

/* ============================================================
   داشبورد آماری + روابط عمومی + مرکز اعلان‌ها + لاگ فعالیت
   ============================================================ */
function computeSatisfactionPercent(donors) {
  const scores = donors.filter((d) => d.survey).map((d) => d.survey.overallSatisfaction).filter(Boolean);
  if (scores.length === 0) return null;
  const avg = scores.reduce((a, b) => a + b, 0) / scores.length;
  return Math.round((avg / 5) * 100);
}
function computeReferralBreakdown(donors) {
  const counts = {};
  donors.forEach((d) => { if (d.survey && d.survey.referralSource) counts[d.survey.referralSource] = (counts[d.survey.referralSource] || 0) + 1; });
  const total = Object.values(counts).reduce((a, b) => a + b, 0) || 1;
  return Object.entries(counts).map(([source, count]) => ({ source, count, percent: Math.round((count / total) * 100) }));
}
function computeCancelReasons(donors) {
  const counts = {};
  donors.forEach((d) => d.appointments.forEach((a) => {
    if (a.status === "cancelled") { const key = a.cancelReason || "بدون علت ثبت‌شده"; counts[key] = (counts[key] || 0) + 1; }
  }));
  return Object.entries(counts).map(([reason, count]) => ({ reason, count }));
}
function computeMonthlyTrend(donors) {
  const buckets = {};
  donors.forEach((d) => {
    if (!d.survey) return;
    const key = new Date(d.survey.completedAt).toISOString().slice(0, 7);
    if (!buckets[key]) buckets[key] = [];
    if (d.survey.overallSatisfaction) buckets[key].push(d.survey.overallSatisfaction);
  });
  return Object.entries(buckets).sort(([a], [b]) => a.localeCompare(b)).map(([month, vals]) => ({
    month, avg: Math.round((vals.reduce((a, b) => a + b, 0) / vals.length) * 10) / 10,
  }));
}

adminRouter2.get("/dashboard/stats", (req, res) => {
  const db = readDb();
  const now = new Date();
  const startOfDay = new Date(now.getFullYear(), now.getMonth(), now.getDate());
  const donors = db.donors;
  const allAppointments = donors.flatMap((d) => d.appointments);
  res.json({
    newRegistrations: donors.filter((d) => new Date(d.createdAt) >= startOfDay).length,
    awaitingLab: donors.filter((d) => d.status === "awaiting_lab").length,
    activePanels: donors.filter((d) => d.labApprovedAt).length,
    todaysAppointments: allAppointments.filter((a) => a.status !== "cancelled" && new Date(a.confirmedDate || a.requestedDate) >= startOfDay && new Date(a.confirmedDate || a.requestedDate) < new Date(startOfDay.getTime() + 86400000)).length,
    totalDonations: allAppointments.filter((a) => a.donated === true).length,
    satisfactionPercent: computeSatisfactionPercent(donors),
    referralBreakdown: computeReferralBreakdown(donors),
  });
});

adminRouter2.get("/dashboard/pr", (req, res) => {
  const db = readDb();
  const surveys = db.donors.filter((d) => d.survey).map((d) => d.survey);
  const categories = ["securityBehavior", "receptionBehavior", "doctorBehavior", "nurseBehavior", "staffBehavior", "orderSpeed", "cleanliness", "ambiance", "overallSatisfaction"];
  const averages = {};
  categories.forEach((c) => {
    const vals = surveys.map((s) => s[c]).filter(Boolean);
    averages[c] = vals.length ? Math.round((vals.reduce((a, b) => a + b, 0) / vals.length) * 10) / 10 : null;
  });
  res.json({
    averages,
    referralBreakdown: computeReferralBreakdown(db.donors),
    complaints: surveys.filter((s) => s.freeText && s.freeText.trim()).map((s) => ({ text: s.freeText, date: s.completedAt })).sort((a, b) => new Date(b.date) - new Date(a.date)),
    trend: computeMonthlyTrend(db.donors),
  });
});

adminRouter2.get("/dashboard/crm", (req, res) => {
  const db = readDb();
  const donors = db.donors;
  const now = new Date();
  const startOfDay = new Date(now.getFullYear(), now.getMonth(), now.getDate());
  const callsToday = db.activityLog.filter((a) => a.action === "note_call" && new Date(a.createdAt) >= startOfDay).length;
  res.json({
    activeDonors: donors.filter((d) => !["blocked", "inactive"].includes(d.status)).length,
    inactiveDonors: donors.filter((d) => d.status === "inactive").length,
    needsFollowup: donors.filter((d) => d.status === "needs_followup").length,
    callsToday,
    pendingReminders: donors.reduce((sum, d) => sum + d.reminders.filter((r) => !r.done).length, 0),
    avgSatisfaction: computeSatisfactionPercent(donors),
    cancelReasons: computeCancelReasons(donors),
    referralBreakdown: computeReferralBreakdown(donors),
  });
});

adminRouter2.get("/notifications-center", (req, res) => {
  const db = readDb();
  const alerts = domain.computeAlerts(db);
  const dueReminders = [];
  db.donors.forEach((d) => d.reminders.forEach((r) => { if (!r.done && new Date(r.dueDate) <= new Date()) dueReminders.push({ ...r, donorName: `${d.firstName} ${d.lastName}`, donorPhone: d.phone }); }));
  const pendingLab = db.donors.filter((d) => d.status === "awaiting_lab").map((d) => ({ donorName: `${d.firstName} ${d.lastName}`, donorPhone: d.phone, since: d.survey ? d.survey.completedAt : d.createdAt }));
  const newAppointmentRequests = [];
  db.donors.forEach((d) => d.appointments.forEach((a) => { if (a.status === "requested") newAppointmentRequests.push({ ...a, donorName: `${d.firstName} ${d.lastName}`, donorPhone: d.phone }); }));
  const followupsNeeded = [];
  db.donors.forEach((d) => domain.pendingFollowUps(d).forEach((f) => followupsNeeded.push({ ...f, donorName: `${d.firstName} ${d.lastName}`, donorPhone: d.phone })));
  const newSurveys = db.donors.filter((d) => d.survey).sort((a, b) => new Date(b.survey.completedAt) - new Date(a.survey.completedAt)).slice(0, 10).map((d) => ({ donorName: `${d.firstName} ${d.lastName}`, donorPhone: d.phone, date: d.survey.completedAt }));

  res.json({ alerts, dueReminders, pendingLab, newAppointmentRequests, followupsNeeded, newSurveys });
});

adminRouter2.get("/activity-log", requireAdmin, (req, res) => {
  const db = readDb();
  res.json([...db.activityLog].sort((a, b) => new Date(b.createdAt) - new Date(a.createdAt)).slice(0, 500));
});

/* ---------- خروجی CSV (سازگار با اکسل) ---------- */
adminRouter2.get("/export/donors.csv", requireAdmin, (req, res) => {
  const db = readDb();
  const rows = [["نام", "نام‌خانوادگی", "موبایل", "سن", "وضعیت", "تعداد اهدا", "تاریخ ثبت‌نام"]];
  db.donors.forEach((d) => {
    rows.push([d.firstName, d.lastName, d.phone, d.age, domain.STATUS_LABELS[d.status] || d.status,
      d.appointments.filter((a) => a.donated === true).length, d.createdAt]);
  });
  const csv = "\uFEFF" + rows.map((r) => r.map((c) => `"${String(c).replace(/"/g, '""')}"`).join(",")).join("\r\n");
  res.setHeader("Content-Type", "text/csv; charset=utf-8");
  res.setHeader("Content-Disposition", "attachment; filename=donors.csv");
  res.send(csv);
});

app.use("/api/admin", adminRouter2);

/* ============================================================
   بخش ۱۰: فرانت‌اند (HTML + JS داخل همین فایل، به‌صورت base64)
   ============================================================ */
const INDEX_HTML = Buffer.from("PCFET0NUWVBFIGh0bWw+CjxodG1sIGxhbmc9ImZhIiBkaXI9InJ0bCI+CjxoZWFkPgo8bWV0YSBjaGFyc2V0PSJVVEYtOCIgLz4KPG1ldGEgbmFtZT0idmlld3BvcnQiIGNvbnRlbnQ9IndpZHRoPWRldmljZS13aWR0aCwgaW5pdGlhbC1zY2FsZT0xLjAsIG1heGltdW0tc2NhbGU9MSIgLz4KPHRpdGxlPtmF2LHaqdiyINin2YfYr9inINm+2YTYp9iz2YXYpyDZhtmI24zZhiDZvtmE2KfYs9mF2Kcg2b7ZiNix2Kcg2K/Yp9ix2Yg8L3RpdGxlPgo8bGluayByZWw9InByZWNvbm5lY3QiIGhyZWY9Imh0dHBzOi8vZm9udHMuZ29vZ2xlYXBpcy5jb20iIC8+CjxsaW5rIHJlbD0icHJlY29ubmVjdCIgaHJlZj0iaHR0cHM6Ly9mb250cy5nc3RhdGljLmNvbSIgY3Jvc3NvcmlnaW4gLz4KPGxpbmsgaHJlZj0iaHR0cHM6Ly9mb250cy5nb29nbGVhcGlzLmNvbS9jc3MyP2ZhbWlseT1WYXppcm1hdG46d2dodEA0MDA7NTAwOzYwMDs3MDA7ODAwJmRpc3BsYXk9c3dhcCIgcmVsPSJzdHlsZXNoZWV0IiAvPgo8c2NyaXB0IHNyYz0iaHR0cHM6Ly9jZG4udGFpbHdpbmRjc3MuY29tIj48L3NjcmlwdD4KPHNjcmlwdCBzcmM9Imh0dHBzOi8vdW5wa2cuY29tL2x1Y2lkZUBsYXRlc3QvZGlzdC91bWQvbHVjaWRlLmpzIj48L3NjcmlwdD4KPHNjcmlwdD4KICB0YWlsd2luZC5jb25maWcgPSB7CiAgICB0aGVtZTogewogICAgICBleHRlbmQ6IHsKICAgICAgICBmb250RmFtaWx5OiB7IHNhbnM6IFsiVmF6aXJtYXRuIiwgIlRhaG9tYSIsICJBcmlhbCIsICJzYW5zLXNlcmlmIl0gfSwKICAgICAgfSwKICAgIH0sCiAgfTsKPC9zY3JpcHQ+CjxzdHlsZT4KICBodG1sIHsgc2Nyb2xsLWJlaGF2aW9yOiBzbW9vdGg7IH0KICBib2R5IHsgZm9udC1mYW1pbHk6ICJWYXppcm1hdG4iLCBUYWhvbWEsICJTZWdvZSBVSSIsIEFyaWFsLCBzYW5zLXNlcmlmOyBiYWNrZ3JvdW5kOiByYWRpYWwtZ3JhZGllbnQoY2lyY2xlIGF0IDE1JSAwJSwgI2YwZjlmNiAwJSwgI2ZhZmFmOSA0NSUpOyB9CiAgLmZhZGUtaW4geyBhbmltYXRpb246IGZhZGVJbiAuMjVzIGVhc2U7IH0KICBAa2V5ZnJhbWVzIGZhZGVJbiB7IGZyb20geyBvcGFjaXR5OiAwOyB0cmFuc2Zvcm06IHRyYW5zbGF0ZVkoOHB4KTsgfSB0byB7IG9wYWNpdHk6IDE7IHRyYW5zZm9ybTogdHJhbnNsYXRlWSgwKTsgfSB9CiAgOjotd2Via2l0LXNjcm9sbGJhciB7IHdpZHRoOiA4cHg7IGhlaWdodDogOHB4OyB9CiAgOjotd2Via2l0LXNjcm9sbGJhci10aHVtYiB7IGJhY2tncm91bmQ6ICNkNmQzZDE7IGJvcmRlci1yYWRpdXM6IDhweDsgfQogIDo6LXdlYmtpdC1zY3JvbGxiYXItdHJhY2sgeyBiYWNrZ3JvdW5kOiB0cmFuc3BhcmVudDsgfQogIFtkYXRhLWx1Y2lkZV0geyB3aWR0aDogMWVtOyBoZWlnaHQ6IDFlbTsgfQogIEBtZWRpYSBwcmludCB7IC5uby1wcmludCB7IGRpc3BsYXk6IG5vbmUgIWltcG9ydGFudDsgfSB9Cjwvc3R5bGU+CjwvaGVhZD4KPGJvZHkgY2xhc3M9ImJnLXN0b25lLTUwIG1pbi1oLXNjcmVlbiI+CiAgPGRpdiBpZD0iYXBwIiBjbGFzcz0ibWluLWgtc2NyZWVuIj48L2Rpdj4KICA8c2NyaXB0IHNyYz0iL2FwcC5qcyI+PC9zY3JpcHQ+CjwvYm9keT4KPC9odG1sPgo=", "base64").toString("utf8");
const APP_JS = Buffer.from("LyogPT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09CiAgINmF2LHaqdiyINin2YfYr9inINm+2YTYp9iz2YXYpyDZhtmI24zZhiDZvtmE2KfYs9mF2Kcg2b7ZiNix2Kcg2K/Yp9ix2Ygg4oCUINm+2YbZhCBDUk0KICAgPT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09ICovCgphc3luYyBmdW5jdGlvbiBhcGkobWV0aG9kLCB1cmwsIGJvZHkpIHsKICBjb25zdCByZXMgPSBhd2FpdCBmZXRjaCh1cmwsIHsKICAgIG1ldGhvZCwgaGVhZGVyczogeyAiQ29udGVudC1UeXBlIjogImFwcGxpY2F0aW9uL2pzb24iIH0sIGNyZWRlbnRpYWxzOiAic2FtZS1vcmlnaW4iLAogICAgYm9keTogYm9keSAhPT0gdW5kZWZpbmVkID8gSlNPTi5zdHJpbmdpZnkoYm9keSkgOiB1bmRlZmluZWQsCiAgfSk7CiAgbGV0IGRhdGEgPSBudWxsOwogIHRyeSB7IGRhdGEgPSBhd2FpdCByZXMuanNvbigpOyB9IGNhdGNoIChlKSB7fQogIGlmICghcmVzLm9rKSB0aHJvdyBuZXcgRXJyb3IoKGRhdGEgJiYgZGF0YS5lcnJvcikgfHwgItiu2LfYp9uMINmG2KfYtNmG2KfYrtiq2Ycg2LPYsdmI2LEiKTsKICByZXR1cm4gZGF0YTsKfQoKZnVuY3Rpb24gZXNjKHN0cikgeyBjb25zdCBkID0gZG9jdW1lbnQuY3JlYXRlRWxlbWVudCgiZGl2Iik7IGQudGV4dENvbnRlbnQgPSBzdHIgPT0gbnVsbCA/ICIiIDogU3RyaW5nKHN0cik7IHJldHVybiBkLmlubmVySFRNTDsgfQoKY29uc3QgRkFfTU9OVEhTID0gWyLZgdix2YjYsdiv24zZhiIsItin2LHYr9uM2KjZh9i02KoiLCLYrtix2K/Yp9ivIiwi2KrbjNixIiwi2YXYsdiv2KfYryIsIti02YfYsduM2YjYsSIsItmF2YfYsSIsItii2KjYp9mGIiwi2KLYsNixIiwi2K/bjCIsItio2YfZhdmGIiwi2KfYs9mB2YbYryJdOwpjb25zdCBGQV9XRUVLREFZUyA9IFsi24zaqdi02YbYqNmHIiwi2K/ZiNi02YbYqNmHIiwi2LPZh+KAjNi02YbYqNmHIiwi2obZh9in2LHYtNmG2KjZhyIsItm+2YbYrNi02YbYqNmHIiwi2KzZhdi52YciLCLYtNmG2KjZhyJdOwpmdW5jdGlvbiBmYURpZ2l0cyhuKSB7IGNvbnN0IG1hcD17MDoi27AiLDE6ItuxIiwyOiLbsiIsMzoi27MiLDQ6Itu0Iiw1OiLbtSIsNjoi27YiLDc6Itu3Iiw4OiLbuCIsOToi27kifTsgcmV0dXJuIFN0cmluZyhuKS5yZXBsYWNlKC9bMC05XS9nLChjKT0+bWFwW2NdKTsgfQpmdW5jdGlvbiBnVG9KYWxhbGkoZ3ksIGdtLCBnZCkgewogIGNvbnN0IGdfZF9tPVswLDMxLDU5LDkwLDEyMCwxNTEsMTgxLDIxMiwyNDMsMjczLDMwNCwzMzRdOwogIGxldCBneTIgPSBnbT4yP2d5KzE6Z3k7CiAgbGV0IGRheXMgPSAzNTU2NjYrMzY1Kmd5K01hdGguZmxvb3IoKGd5MiszKS80KS1NYXRoLmZsb29yKChneTIrOTkpLzEwMCkrTWF0aC5mbG9vcigoZ3kyKzM5OSkvNDAwKStnZCtnX2RfbVtnbS0xXTsKICBsZXQgankgPSAtMTU5NSszMypNYXRoLmZsb29yKGRheXMvMTIwNTMpOyBkYXlzJT0xMjA1MzsKICBqeSArPSA0Kk1hdGguZmxvb3IoZGF5cy8xNDYxKTsgZGF5cyU9MTQ2MTsKICBpZiAoZGF5cz4zNjUpeyBqeSs9TWF0aC5mbG9vcigoZGF5cy0xKS8zNjUpOyBkYXlzPShkYXlzLTEpJTM2NTsgfQogIGxldCBqbSxqZDsKICBpZiAoZGF5czwxODYpeyBqbT0xK01hdGguZmxvb3IoZGF5cy8zMSk7IGpkPTErKGRheXMlMzEpOyB9IGVsc2UgeyBqbT03K01hdGguZmxvb3IoKGRheXMtMTg2KS8zMCk7IGpkPTErKChkYXlzLTE4NiklMzApOyB9CiAgcmV0dXJuIFtqeSxqbSxqZF07Cn0KZnVuY3Rpb24gamFsYWxpUGFydHMoZGF0ZUlucHV0KSB7CiAgY29uc3QgZCA9IG5ldyBEYXRlKGRhdGVJbnB1dCk7CiAgY29uc3QgW2p5LGptLGpkXSA9IGdUb0phbGFsaShkLmdldEZ1bGxZZWFyKCksIGQuZ2V0TW9udGgoKSsxLCBkLmdldERhdGUoKSk7CiAgcmV0dXJuIHsgeWVhcjoganksIG1vbnRoOiBqbSwgZGF5OiBqZCwgbW9udGhOYW1lOiBGQV9NT05USFNbam0tMV0sIHdlZWtkYXk6IEZBX1dFRUtEQVlTW2QuZ2V0RGF5KCldLCBfZDogZCB9Owp9CmZ1bmN0aW9uIGZtdERhdGUoZGF0ZUlucHV0KSB7IGlmICghZGF0ZUlucHV0KSByZXR1cm4gIi0iOyBjb25zdCBqPWphbGFsaVBhcnRzKGRhdGVJbnB1dCk7IHJldHVybiBgJHtqLndlZWtkYXl9ICR7ZmFEaWdpdHMoai5kYXkpfSAke2oubW9udGhOYW1lfSAke2ZhRGlnaXRzKGoueWVhcil9YDsgfQpmdW5jdGlvbiBmbXREYXRlU2hvcnQoZGF0ZUlucHV0KSB7IGlmICghZGF0ZUlucHV0KSByZXR1cm4gIi0iOyBjb25zdCBqPWphbGFsaVBhcnRzKGRhdGVJbnB1dCk7IHJldHVybiBgJHtmYURpZ2l0cyhqLmRheSl9ICR7ai5tb250aE5hbWV9ICR7ZmFEaWdpdHMoai55ZWFyKX1gOyB9CmZ1bmN0aW9uIGZtdERhdGVUaW1lKGRhdGVJbnB1dCkgeyBpZiAoIWRhdGVJbnB1dCkgcmV0dXJuICItIjsgY29uc3Qgaj1qYWxhbGlQYXJ0cyhkYXRlSW5wdXQpOyBjb25zdCBoaD1TdHJpbmcoai5fZC5nZXRIb3VycygpKS5wYWRTdGFydCgyLCIwIik7IGNvbnN0IG1tPVN0cmluZyhqLl9kLmdldE1pbnV0ZXMoKSkucGFkU3RhcnQoMiwiMCIpOyByZXR1cm4gYCR7ZmFEaWdpdHMoai5kYXkpfSAke2oubW9udGhOYW1lfdiMICR7ZmFEaWdpdHMoaGgpfToke2ZhRGlnaXRzKG1tKX1gOyB9CmZ1bmN0aW9uIHRvZGF5SVNPRGF0ZSgpIHsgY29uc3QgZD1uZXcgRGF0ZSgpOyByZXR1cm4gYCR7ZC5nZXRGdWxsWWVhcigpfS0ke1N0cmluZyhkLmdldE1vbnRoKCkrMSkucGFkU3RhcnQoMiwiMCIpfS0ke1N0cmluZyhkLmdldERhdGUoKSkucGFkU3RhcnQoMiwiMCIpfWA7IH0KCmNvbnN0IFdFRUtEQVlfTEFCRUxTID0gWyLbjNqp2LTZhtio2YciLCLYr9mI2LTZhtio2YciLCLYs9mH4oCM2LTZhtio2YciLCLahtmH2KfYsdi02YbYqNmHIiwi2b7Zhtis2LTZhtio2YciLCLYrNmF2LnZhyIsIti02YbYqNmHIl07CmNvbnN0IFJFRkVSUkFMX09QVElPTlMgPSBbItix2YjYp9io2Lcg2LnZhdmI2YXbjCIsItin24zZhtiz2KrYp9qv2LHYp9mFIiwi2YXYudix2YHbjCDYr9mI2LPYqtin2YYg2Ygg2KLYtNmG2KfbjNin2YYiLCLYqtio2YTbjNi62KfYqiDZhdit24zYt9uMIiwi2KzYs9iq2KzZiNuMINin24zZhtiq2LHZhtiqIiwi2YXYsdin2KzYudmHINmC2KjZhNuMIiwi2LPYp9uM2LEiXTsKY29uc3QgU1VSVkVZX0NBVEVHT1JJRVMgPSBbCiAgWyJzZWN1cml0eUJlaGF2aW9yIiwgItmG2K3ZiNmH4oCM24wg2KjYsdiu2YjYsdivINit2LHYp9iz2KoiXSwKICBbInJlY2VwdGlvbkJlaGF2aW9yIiwgItmG2K3ZiNmH4oCM24wg2KjYsdiu2YjYsdivINm+2LDbjNix2LQiXSwKICBbImRvY3RvckJlaGF2aW9yIiwgItix2YHYqtin2LEg2b7Ysti02qkiXSwKICBbIm51cnNlQmVoYXZpb3IiLCAi2LHZgdiq2KfYsSDZvtix2LPYqtin2LHYp9mGIl0sCiAgWyJzdGFmZkJlaGF2aW9yIiwgItix2YHYqtin2LEg2LPYp9uM2LEg2qnYp9ix2qnZhtin2YYiXSwKICBbIm9yZGVyU3BlZWQiLCAi2YbYuNmFINmIINiz2LHYudiqINin2YbYrNin2YUg2qnYp9ixIl0sCiAgWyJjbGVhbmxpbmVzcyIsICLYqtmF24zYstuMINmIINmG2LjYp9mB2Kog2YXYsdqp2LIiXSwKICBbImFtYmlhbmNlIiwgItii2LHYp9mF2LQg2Ygg2YHYttin24wg2YXYrduM2LciXSwKICBbIm92ZXJhbGxTYXRpc2ZhY3Rpb24iLCAi2YXbjNiy2KfZhiDYsdi22KfbjNiqINqp2YTbjCDYp9iyINin2YjZhNuM2YYg2YXYsdin2KzYudmHIl0sCl07CmNvbnN0IFNUQVRVU19MQUJFTFMgPSB7CiAgcmVnaXN0ZXJlZDogItir2KjYquKAjNmG2KfZhSDYp9mI2YTbjNmHIiwgYXdhaXRpbmdfbGFiOiAi2YXZhtiq2LjYsSDYrNmI2KfYqCDYotiy2YXYp9uM2LQiLCByZWFkeTogItii2YXYp9iv2Ycg2KrYuduM24zZhiDZhtmI2KjYqiIsCiAgYm9va2VkOiAi2YbZiNio2Kog2LHYstix2Ygg2LTYr9mHIiwgdmlzaXRlZDogItmF2LHYp9is2LnZhyDaqdix2K8iLCBkb25hdGVkOiAi2KfZh9iv2Kcg2KfZhtis2KfZhSDYtNivIiwKICBuZWVkc19mb2xsb3d1cDogItmG24zYp9iy2YXZhtivINm+24zar9uM2LHbjCIsIHVucmVzcG9uc2l2ZTogIti52K/ZhSDZvtin2LPYrtqv2YjbjNuMIiwgaW5hY3RpdmU6ICLYutuM2LHZgdi52KfZhCIsIGJsb2NrZWQ6ICLZhdiz2K/ZiNivINi02K/ZhyIsCn07CmNvbnN0IFJFTUlOREVSX1RZUEVTID0gWyLYqtmF2KfYsyDYqtmE2YHZhtuMIiwgItin2LHYs9in2YQg2b7bjNin2YXaqSIsICLYr9i52YjYqiDYqNix2KfbjCDZhdix2KfYrNi52YciLCAi2b7bjNqv24zYsduMINmG2KrbjNis2Ycg2KLYstmF2KfbjNi0IiwgItio2LHYsdiz24wg2YjYtti524zYqiDYs9mE2KfZhdiqIl07Cgpjb25zdCBzdGF0ZSA9IHsKICBzY3JlZW46ICJsYW5kaW5nIiwKICB0b2FzdDogbnVsbCwgZXJyb3JNc2c6IG51bGwsCiAgZG9ub3I6IG51bGwsIGRvbm9yTm90aWZpY2F0aW9uczogW10sCiAgc3RhZmY6IG51bGwsCiAgZm9ybToge30sCiAgYWRtaW46IHsgZG9ub3JzOiBudWxsLCBxOiAiIiwgc2VsZWN0ZWRQaG9uZTogbnVsbCwgc2VsZWN0ZWREb25vcjogbnVsbCwgc2V0dGluZ3M6IG51bGwsIHN0YWZmTGlzdDogbnVsbCwgc3RhdHM6IG51bGwsIHByOiBudWxsLCBjcm06IG51bGwsIG5vdGlmQ2VudGVyOiBudWxsLCBhY3Rpdml0eUxvZzogbnVsbCwgYXBwb2ludG1lbnRzOiBudWxsLCBzbG90RGF0ZTogbnVsbCwgc2xvdHM6IG51bGwgfSwKICBmb3JjZWRQd0NoYW5nZTogZmFsc2UsCn07CgpmdW5jdGlvbiBzZXRTY3JlZW4ocywgcmVzZXRGb3JtID0gdHJ1ZSkgeyBzdGF0ZS5zY3JlZW4gPSBzOyBpZiAocmVzZXRGb3JtKSBzdGF0ZS5mb3JtID0ge307IHN0YXRlLmVycm9yTXNnID0gbnVsbDsgcmVuZGVyKCk7IHdpbmRvdy5zY3JvbGxUbygwLDApOyB9CmZ1bmN0aW9uIHNob3dUb2FzdChtc2csIHRvbmU9ImVtZXJhbGQiKSB7IHN0YXRlLnRvYXN0ID0geyBtc2csIHRvbmUgfTsgcmVuZGVyKCk7IHNldFRpbWVvdXQoKCk9Pnsgc3RhdGUudG9hc3Q9bnVsbDsgcmVuZGVyKCk7IH0sIDMyMDApOyB9CgovKiA9PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT0KICAg2YLYt9i52YfigIzZh9in24wg2LHYp9io2Lcg2qnYp9ix2KjYsduMCiAgID09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PSAqLwpmdW5jdGlvbiBJY29uKG5hbWUsIGNscz0iIikgeyByZXR1cm4gYDxpIGRhdGEtbHVjaWRlPSIke25hbWV9IiBjbGFzcz0iJHtjbHN9Ij48L2k+YDsgfQpmdW5jdGlvbiBDYXJkKGlubmVyLCBjbHM9IiIpIHsgcmV0dXJuIGA8ZGl2IGNsYXNzPSJiZy13aGl0ZSByb3VuZGVkLTJ4bCBzaGFkb3ctWzBfMXB4XzNweF9yZ2JhKDE1LDIzLDIyLDAuMDYpLDBfOHB4XzI0cHhfLTEycHhfcmdiYSgxNSwyMywyMiwwLjEwKV0gYm9yZGVyIGJvcmRlci1zdG9uZS0yMDAvNzAgJHtjbHN9Ij4ke2lubmVyfTwvZGl2PmA7IH0KZnVuY3Rpb24gQmFkZ2UodGV4dCwgdG9uZT0ic2xhdGUiKSB7CiAgY29uc3QgdG9uZXMgPSB7IHNsYXRlOiJiZy1zdG9uZS0xMDAgdGV4dC1zdG9uZS02MDAiLCBhbWJlcjoiYmctYW1iZXItMTAwIHRleHQtYW1iZXItODAwIiwgZW1lcmFsZDoiYmctZW1lcmFsZC0xMDAgdGV4dC1lbWVyYWxkLTcwMCIsIHJvc2U6ImJnLXJvc2UtMTAwIHRleHQtcm9zZS03MDAiLCB0ZWFsOiJiZy10ZWFsLTEwMCB0ZXh0LXRlYWwtODAwIiB9OwogIHJldHVybiBgPHNwYW4gY2xhc3M9InB4LTIuNSBweS0xIHJvdW5kZWQtZnVsbCB0ZXh0LXhzIGZvbnQtc2VtaWJvbGQgJHt0b25lc1t0b25lXX0iPiR7ZXNjKHRleHQpfTwvc3Bhbj5gOwp9CmZ1bmN0aW9uIFByaW1hcnlCdXR0b24obGFiZWwsIGFjdGlvbiwgb3B0cz17fSkgewogIGNvbnN0IGRhdGEgPSBvcHRzLmRhdGEgPyBPYmplY3QuZW50cmllcyhvcHRzLmRhdGEpLm1hcCgoW2ssdl0pPT5gZGF0YS0ke2t9PSIke2VzYyh2KX0iYCkuam9pbigiICIpIDogIiI7CiAgcmV0dXJuIGA8YnV0dG9uIGRhdGEtYWN0aW9uPSIke2FjdGlvbn0iICR7ZGF0YX0gJHtvcHRzLmRpc2FibGVkPyJkaXNhYmxlZCI6IiJ9IGNsYXNzPSJ3LWZ1bGwgcHktMy41IHJvdW5kZWQteGwgZm9udC1ib2xkIHRleHQtd2hpdGUgYmctZ3JhZGllbnQtdG8tbCBmcm9tLWFtYmVyLTUwMCB0by1hbWJlci02MDAgaG92ZXI6ZnJvbS1hbWJlci02MDAgaG92ZXI6dG8tYW1iZXItNzAwIGRpc2FibGVkOmZyb20tc3RvbmUtMzAwIGRpc2FibGVkOnRvLXN0b25lLTMwMCBkaXNhYmxlZDpjdXJzb3Itbm90LWFsbG93ZWQgYWN0aXZlOnNjYWxlLVswLjk5XSB0cmFuc2l0aW9uLWFsbCBzaGFkb3ctbGcgc2hhZG93LWFtYmVyLTUwMC8yMCBkaXNhYmxlZDpzaGFkb3ctbm9uZSAke29wdHMuY2xhc3NOYW1lfHwiIn0iPiR7ZXNjKGxhYmVsKX08L2J1dHRvbj5gOwp9CmZ1bmN0aW9uIFNtYWxsQnV0dG9uKGxhYmVsLCBhY3Rpb24sIG9wdHM9e30pIHsKICBjb25zdCBkYXRhID0gb3B0cy5kYXRhID8gT2JqZWN0LmVudHJpZXMob3B0cy5kYXRhKS5tYXAoKFtrLHZdKT0+YGRhdGEtJHtrfT0iJHtlc2Modil9ImApLmpvaW4oIiAiKSA6ICIiOwogIGNvbnN0IHRvbmUgPSBvcHRzLnRvbmUgfHwgInRlYWwiOwogIGNvbnN0IHRvbmVzID0geyB0ZWFsOiJiZy10ZWFsLTUwIHRleHQtdGVhbC04MDAgaG92ZXI6YmctdGVhbC0xMDAiLCByb3NlOiJiZy1yb3NlLTUwIHRleHQtcm9zZS03MDAgaG92ZXI6Ymctcm9zZS0xMDAiLCBlbWVyYWxkOiJiZy1lbWVyYWxkLTYwMCB0ZXh0LXdoaXRlIGhvdmVyOmJnLWVtZXJhbGQtNzAwIHNoYWRvdy1zbSBzaGFkb3ctZW1lcmFsZC02MDAvMzAiLCBzdG9uZToiYmctc3RvbmUtMTAwIHRleHQtc3RvbmUtNjAwIGhvdmVyOmJnLXN0b25lLTIwMCIgfTsKICByZXR1cm4gYDxidXR0b24gZGF0YS1hY3Rpb249IiR7YWN0aW9ufSIgJHtkYXRhfSBjbGFzcz0icHgtMyBweS0yIHJvdW5kZWQtbGcgdGV4dC14cyBmb250LWJvbGQgdHJhbnNpdGlvbi1jb2xvcnMgJHt0b25lc1t0b25lXX0gJHtvcHRzLmNsYXNzTmFtZXx8IiJ9Ij4ke2VzYyhsYWJlbCl9PC9idXR0b24+YDsKfQpmdW5jdGlvbiBHaG9zdEJ1dHRvbihsYWJlbCwgYWN0aW9uLCBvcHRzPXt9KSB7CiAgY29uc3QgZGF0YSA9IG9wdHMuZGF0YSA/IE9iamVjdC5lbnRyaWVzKG9wdHMuZGF0YSkubWFwKChbayx2XSk9PmBkYXRhLSR7a309IiR7ZXNjKHYpfSJgKS5qb2luKCIgIikgOiAiIjsKICByZXR1cm4gYDxidXR0b24gZGF0YS1hY3Rpb249IiR7YWN0aW9ufSIgJHtkYXRhfSBjbGFzcz0idy1mdWxsIHB5LTMgcm91bmRlZC14bCBmb250LXNlbWlib2xkIHRleHQtdGVhbC04MDAgYmctd2hpdGUgYm9yZGVyIGJvcmRlci10ZWFsLTEwMCBob3Zlcjpib3JkZXItdGVhbC0zMDAgaG92ZXI6YmctdGVhbC01MC82MCB0cmFuc2l0aW9uLWNvbG9ycyBzaGFkb3ctc20iPiR7bGFiZWx9PC9idXR0b24+YDsKfQpmdW5jdGlvbiBUb3BCYXIodGl0bGUsIGJhY2tBY3Rpb24sIHJpZ2h0PSIiKSB7CiAgcmV0dXJuIGA8ZGl2IGNsYXNzPSJmbGV4IGl0ZW1zLWNlbnRlciBqdXN0aWZ5LWJldHdlZW4gbWItNSI+CiAgICAke2JhY2tBY3Rpb24gPyBgPGJ1dHRvbiBkYXRhLWFjdGlvbj0iJHtiYWNrQWN0aW9ufSIgY2xhc3M9InctOSBoLTkgcm91bmRlZC1mdWxsIGZsZXggaXRlbXMtY2VudGVyIGp1c3RpZnktY2VudGVyIHRleHQtdGVhbC04MDAgYmctd2hpdGUgYm9yZGVyIGJvcmRlci1zdG9uZS0yMDAgc2hhZG93LXNtIGhvdmVyOmJnLXN0b25lLTUwIj4ke0ljb24oImFycm93LXJpZ2h0Iiwidy00IGgtNCIpfTwvYnV0dG9uPmAgOiBgPGRpdiBjbGFzcz0idy05Ij48L2Rpdj5gfQogICAgPGgxIGNsYXNzPSJmb250LWJvbGQgdGV4dC1sZyB0ZXh0LXRlYWwtOTUwIj4ke2VzYyh0aXRsZSl9PC9oMT4KICAgIDxkaXYgY2xhc3M9InctOSBmbGV4IGp1c3RpZnktZW5kIj4ke3JpZ2h0fTwvZGl2PgogIDwvZGl2PmA7Cn0KZnVuY3Rpb24gU2NhbGVJbnB1dChuYW1lLCBjdXJyZW50KSB7CiAgY29uc3QgdiA9IHN0YXRlLmZvcm1bbmFtZV0gfHwgMDsKICByZXR1cm4gYDxkaXYgY2xhc3M9ImZsZXgganVzdGlmeS1iZXR3ZWVuIGdhcC0xLjUiPiR7WzEsMiwzLDQsNV0ubWFwKChuKT0+YAogICAgPGJ1dHRvbiBkYXRhLWFjdGlvbj0ic2V0Rm9ybSIgZGF0YS1rZXk9IiR7bmFtZX0iIGRhdGEtdmFsdWU9IiR7bn0iIGNsYXNzPSJmbGV4LTEgcHktMi41IHJvdW5kZWQtbGcgdGV4dC1zbSBmb250LWJvbGQgYm9yZGVyIHRyYW5zaXRpb24tYWxsICR7dj09PW4/ImJnLWdyYWRpZW50LXRvLWIgZnJvbS10ZWFsLTcwMCB0by10ZWFsLTkwMCB0ZXh0LXdoaXRlIGJvcmRlci10ZWFsLTkwMCBzaGFkb3ctbWQgc2hhZG93LXRlYWwtOTAwLzIwIHNjYWxlLTEwNSI6ImJnLXdoaXRlIHRleHQtc3RvbmUtNTAwIGJvcmRlci1zdG9uZS0yMDAgaG92ZXI6Ym9yZGVyLXRlYWwtMzAwIn0iPiR7ZmFEaWdpdHMobil9PC9idXR0b24+CiAgYCkuam9pbigiIil9PC9kaXY+YDsKfQpmdW5jdGlvbiBSYXRpbmdSb3cobGFiZWwsIG5hbWUpIHsgcmV0dXJuIGA8ZGl2PjxwIGNsYXNzPSJ0ZXh0LXNtIHRleHQtc3RvbmUtNzAwIG1iLTIiPiR7ZXNjKGxhYmVsKX08L3A+JHtTY2FsZUlucHV0KG5hbWUpfTwvZGl2PmA7IH0KZnVuY3Rpb24gVG9hc3QodCkgeyBpZighdCkgcmV0dXJuICIiOyBjb25zdCBjbHMgPSB0LnRvbmU9PT0icm9zZSI/ImJnLXJvc2UtNTAgdGV4dC1yb3NlLTcwMCBib3JkZXIgYm9yZGVyLXJvc2UtMjAwIjoiYmctZW1lcmFsZC01MCB0ZXh0LWVtZXJhbGQtNzAwIGJvcmRlciBib3JkZXItZW1lcmFsZC0yMDAiOyByZXR1cm4gYDxkaXYgY2xhc3M9Im1iLTQgcC0zIHJvdW5kZWQteGwgdGV4dC1zbSBmb250LXNlbWlib2xkIHRleHQtY2VudGVyICR7Y2xzfSI+JHtlc2ModC5tc2cpfTwvZGl2PmA7IH0KZnVuY3Rpb24gRXJyb3JCb3gobSkgeyBpZighbSkgcmV0dXJuICIiOyByZXR1cm4gYDxkaXYgY2xhc3M9Im1iLTQgcC0zIHJvdW5kZWQteGwgdGV4dC1zbSBmb250LXNlbWlib2xkIHRleHQtY2VudGVyIGJnLXJvc2UtNTAgdGV4dC1yb3NlLTcwMCBib3JkZXIgYm9yZGVyLXJvc2UtMjAwIj4ke2VzYyhtKX08L2Rpdj5gOyB9CmZ1bmN0aW9uIEJhclJvdyhsYWJlbCwgdmFsdWUsIG1heCwgdG9uZT0iYW1iZXIiKSB7CiAgY29uc3QgcGN0ID0gbWF4ID4gMCA/IE1hdGgucm91bmQoKHZhbHVlL21heCkqMTAwKSA6IDA7CiAgY29uc3QgY29sb3JzID0geyBhbWJlcjoiYmctZ3JhZGllbnQtdG8tbCBmcm9tLWFtYmVyLTQwMCB0by1hbWJlci02MDAiLCB0ZWFsOiJiZy1ncmFkaWVudC10by1sIGZyb20tdGVhbC02MDAgdG8tdGVhbC05MDAiLCBlbWVyYWxkOiJiZy1ncmFkaWVudC10by1sIGZyb20tZW1lcmFsZC00MDAgdG8tZW1lcmFsZC02MDAiLCByb3NlOiJiZy1ncmFkaWVudC10by1sIGZyb20tcm9zZS00MDAgdG8tcm9zZS02MDAiIH07CiAgcmV0dXJuIGA8ZGl2IGNsYXNzPSJtYi0zIj4KICAgIDxkaXYgY2xhc3M9ImZsZXgganVzdGlmeS1iZXR3ZWVuIHRleHQteHMgdGV4dC1zdG9uZS02MDAgbWItMS41Ij48c3Bhbj4ke2VzYyhsYWJlbCl9PC9zcGFuPjxzcGFuIGNsYXNzPSJmb250LWJvbGQgdGV4dC1zdG9uZS04MDAiPiR7ZmFEaWdpdHModmFsdWUpfTwvc3Bhbj48L2Rpdj4KICAgIDxkaXYgY2xhc3M9InctZnVsbCBoLTIuNSBiZy1zdG9uZS0xMDAgcm91bmRlZC1mdWxsIG92ZXJmbG93LWhpZGRlbiI+PGRpdiBjbGFzcz0iJHtjb2xvcnNbdG9uZV19IGgtZnVsbCByb3VuZGVkLWZ1bGwgdHJhbnNpdGlvbi1hbGwgZHVyYXRpb24tNTAwIiBzdHlsZT0id2lkdGg6JHtwY3R9JSI+PC9kaXY+PC9kaXY+CiAgPC9kaXY+YDsKfQpmdW5jdGlvbiBTdGF0Q2FyZChpY29uLCBsYWJlbCwgdmFsdWUpIHsKICByZXR1cm4gQ2FyZChgPGRpdiBjbGFzcz0icC00Ij48ZGl2IGNsYXNzPSJ3LTEwIGgtMTAgcm91bmRlZC14bCBmbGV4IGl0ZW1zLWNlbnRlciBqdXN0aWZ5LWNlbnRlciBtYi0zIGJnLWdyYWRpZW50LXRvLWJyIGZyb20tdGVhbC01MCB0by10ZWFsLTEwMCB0ZXh0LXRlYWwtODAwIj4ke0ljb24oaWNvbiwidy01IGgtNSIpfTwvZGl2PgogICAgPHAgY2xhc3M9InRleHQtMnhsIGZvbnQtZXh0cmFib2xkIHRleHQtdGVhbC05NTAiPiR7ZmFEaWdpdHModmFsdWU9PW51bGw/Ii0iOnZhbHVlKX08L3A+PHAgY2xhc3M9InRleHQteHMgdGV4dC1zdG9uZS00MDAgbXQtMC41Ij4ke2VzYyhsYWJlbCl9PC9wPjwvZGl2PmApOwp9CgovKiA9PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT0KICAg2LXZgdit2YfigIzbjCDZiNix2YjYryDYp9i12YTbjAogICA9PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT0gKi8KZnVuY3Rpb24gc2NyZWVuTGFuZGluZygpIHsKICByZXR1cm4gYDxkaXYgY2xhc3M9Im1pbi1oLXNjcmVlbiBmbGV4IGZsZXgtY29sIGl0ZW1zLWNlbnRlciBqdXN0aWZ5LWNlbnRlciBwLTYgcmVsYXRpdmUgb3ZlcmZsb3ctaGlkZGVuIj4KICAgIDxkaXYgY2xhc3M9ImFic29sdXRlIC10b3AtMjQgLXJpZ2h0LTI0IHctNzIgaC03MiBiZy10ZWFsLTEwMCByb3VuZGVkLWZ1bGwgYmx1ci0zeGwgb3BhY2l0eS02MCI+PC9kaXY+CiAgICA8ZGl2IGNsYXNzPSJhYnNvbHV0ZSAtYm90dG9tLTI0IC1sZWZ0LTI0IHctNzIgaC03MiBiZy1hbWJlci0xMDAgcm91bmRlZC1mdWxsIGJsdXItM3hsIG9wYWNpdHktNjAiPjwvZGl2PgogICAgPGRpdiBjbGFzcz0idy1mdWxsIG1heC13LXNtIGZhZGUtaW4gcmVsYXRpdmUiPgogICAgICA8ZGl2IGNsYXNzPSJmbGV4IGZsZXgtY29sIGl0ZW1zLWNlbnRlciBtYi0xMCI+CiAgICAgICAgPGRpdiBjbGFzcz0idy0yMCBoLTIwIHJvdW5kZWQtM3hsIGJnLWdyYWRpZW50LXRvLWJyIGZyb20tdGVhbC04MDAgdG8tdGVhbC05NTAgZmxleCBpdGVtcy1jZW50ZXIganVzdGlmeS1jZW50ZXIgbWItNSBzaGFkb3cteGwgc2hhZG93LXRlYWwtOTAwLzI1IHJpbmctNCByaW5nLXdoaXRlIj4ke0ljb24oImRyb3BsZXRzIiwidy05IGgtOSB0ZXh0LWFtYmVyLTQwMCIpfTwvZGl2PgogICAgICAgIDxoMSBjbGFzcz0idGV4dC0yeGwgZm9udC1leHRyYWJvbGQgdGV4dC10ZWFsLTk1MCB0ZXh0LWNlbnRlciBsZWFkaW5nLXJlbGF4ZWQiPtmF2LHaqdiyINin2YfYr9inINm+2YTYp9iz2YXYpzxici8+2YbZiNuM2YYg2b7ZhNin2LPZhdinINm+2YjYsdinINiv2KfYsdmIPC9oMT4KICAgICAgICA8cCBjbGFzcz0idGV4dC1zdG9uZS01MDAgdGV4dC1zbSBtdC0yIj7Zhti42LHYs9mG2KzbjNiMINm+2KfbjNi0INiz2YTYp9mF2Kog2Ygg2YXYr9uM2LHbjNiqINmG2YjYqNiqINin2YfYr9in2qnZhtmG2K/ar9in2YY8L3A+CiAgICAgIDwvZGl2PgogICAgICA8ZGl2IGNsYXNzPSJzcGFjZS15LTMiPgogICAgICAgICR7UHJpbWFyeUJ1dHRvbigi2YXZhiDYp9mH2K/Yp9qp2YbZhtiv2YfigIzYp9mFIiwgImdvRG9ub3JBdXRoIil9CiAgICAgICAgJHtHaG9zdEJ1dHRvbihJY29uKCJzaGllbGQiLCJ3LTQgaC00IGlubGluZS1ibG9jayBtbC0xIikgKyAiINmI2LHZiNivINqp2KfYsdqp2YbYp9mGINmF2LHaqdiyIiwgImdvU3RhZmZMb2dpbiIpfQogICAgICA8L2Rpdj4KICAgIDwvZGl2PgogIDwvZGl2PmA7Cn0KCi8qID09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PQogICDZhdiz24zYsSDYp9mH2K/Yp9qp2YbZhtiv2Yc6INmI2LHZiNivINio2Kcg2qnYryDZvtuM2KfZhdqp24wKICAgPT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09ICovCmZ1bmN0aW9uIHNjcmVlbkRvbm9yT3RwUGhvbmUoKSB7CiAgcmV0dXJuIGA8ZGl2IGNsYXNzPSJtYXgtdy1zbSBteC1hdXRvIHAtNSI+CiAgICAke1RvcEJhcigi2YjYsdmI2K8gLyDYq9io2KrigIzZhtin2YUiLCAiZ29MYW5kaW5nIil9JHtFcnJvckJveChzdGF0ZS5lcnJvck1zZyl9CiAgICAke0NhcmQoYDxkaXYgY2xhc3M9InAtNSI+CiAgICAgIDxwIGNsYXNzPSJ0ZXh0LXNtIHRleHQtc3RvbmUtNTAwIG1iLTQiPti02YXYp9ix2Ycg2YXZiNio2KfbjNmEINiu2YjYryDYsdinINmI2KfYsdivINqp2YbbjNivINiq2Kcg2qnYryDYqtin24zbjNivINio2LHYp9iq2YjZhiDYp9ix2LPYp9mEINio2LTZhy48L3A+CiAgICAgIDxpbnB1dCBpZD0icGhvbmVJbnB1dCIgaW5wdXRtb2RlPSJudW1lcmljIiBwbGFjZWhvbGRlcj0iMDl4eHh4eHh4eHgiIGNsYXNzPSJ3LWZ1bGwgYm9yZGVyIGJvcmRlci1zdG9uZS0yMDAgcm91bmRlZC14bCBweC00IHB5LTMgdGV4dC1sZyB0cmFja2luZy13aWRlciB0ZXh0LWNlbnRlciBtYi00IiAvPgogICAgICAke1ByaW1hcnlCdXR0b24oItin2LHYs9in2YQg2qnYryIsICJyZXF1ZXN0T3RwIil9CiAgICA8L2Rpdj5gKX0KICA8L2Rpdj5gOwp9CgpmdW5jdGlvbiBzY3JlZW5Eb25vck90cENvZGUoKSB7CiAgcmV0dXJuIGA8ZGl2IGNsYXNzPSJtYXgtdy1zbSBteC1hdXRvIHAtNSI+CiAgICAke1RvcEJhcigi2qnYryDYqtin24zbjNivIiwgImdvRG9ub3JBdXRoIil9JHtFcnJvckJveChzdGF0ZS5lcnJvck1zZyl9CiAgICAke3N0YXRlLmZvcm0uZGVtb0NvZGUgPyBgPGRpdiBjbGFzcz0ibWItNCBwLTMgcm91bmRlZC14bCB0ZXh0LXNtIGJnLWFtYmVyLTEwMCB0ZXh0LWFtYmVyLTgwMCB0ZXh0LWNlbnRlciI+2obZiNmGINiz2LHZiNuM2LMg2b7bjNin2YXaqSDZh9mG2YjYsiDZiNi12YQg2YbYtNiv2YfYjCDaqdivINio2YfigIzYtdmI2LHYqiDYotiy2YXYp9uM2LTbjCDZh9mF24zZhtis2Kcg2YbYtNmI2YYg2K/Yp9iv2Ycg2YXbjOKAjNi02Yc6IDxiIGNsYXNzPSJ0ZXh0LWxnIj4ke2ZhRGlnaXRzKHN0YXRlLmZvcm0uZGVtb0NvZGUpfTwvYj48L2Rpdj5gIDogYDxkaXYgY2xhc3M9Im1iLTQgcC0zIHJvdW5kZWQteGwgdGV4dC1zbSBiZy10ZWFsLTUwIHRleHQtdGVhbC04MDAgdGV4dC1jZW50ZXIiPtqp2K8g2KrYp9uM24zYryDYqNix2KfbjCAke2VzYyhzdGF0ZS5mb3JtLnBob25lKX0g2b7bjNin2YXaqSDYtNivLjwvZGl2PmB9CiAgICAke0NhcmQoYDxkaXYgY2xhc3M9InAtNSI+CiAgICAgIDxpbnB1dCBpZD0ib3RwSW5wdXQiIGlucHV0bW9kZT0ibnVtZXJpYyIgcGxhY2Vob2xkZXI9Itqp2K8g27Yg2LHZgtmF24wiIGNsYXNzPSJ3LWZ1bGwgYm9yZGVyIGJvcmRlci1zdG9uZS0yMDAgcm91bmRlZC14bCBweC00IHB5LTMgdGV4dC1sZyB0cmFja2luZy13aWRlc3QgdGV4dC1jZW50ZXIgbWItNCIgLz4KICAgICAgJHtQcmltYXJ5QnV0dG9uKCLYqtin24zbjNivIiwgInZlcmlmeU90cCIpfQogICAgPC9kaXY+YCl9CiAgPC9kaXY+YDsKfQoKZnVuY3Rpb24gc2NyZWVuRG9ub3JSZWdpc3RlcigpIHsKICByZXR1cm4gYDxkaXYgY2xhc3M9Im1heC13LXNtIG14LWF1dG8gcC01Ij4KICAgICR7VG9wQmFyKCLYq9io2KrigIzZhtin2YUiLCBudWxsKX0ke0Vycm9yQm94KHN0YXRlLmVycm9yTXNnKX0KICAgICR7Q2FyZChgPGRpdiBjbGFzcz0icC01IHNwYWNlLXktMyI+CiAgICAgIDxwIGNsYXNzPSJ0ZXh0LXNtIHRleHQtc3RvbmUtNTAwIj7Yp9mI2YTbjNmGINit2LbZiNix2KrZiNmG2YchINmE2LfZgdin2Ysg2KfYt9mE2KfYudin2Kog2LLbjNixINix2Ygg2KraqdmF24zZhCDaqdmG24zYry48L3A+CiAgICAgIDxkaXY+PGxhYmVsIGNsYXNzPSJ0ZXh0LXhzIGZvbnQtc2VtaWJvbGQgdGV4dC1zdG9uZS01MDAiPtmG2KfZhTwvbGFiZWw+PGlucHV0IGlkPSJmaXJzdE5hbWVJbnB1dCIgY2xhc3M9InctZnVsbCBib3JkZXIgYm9yZGVyLXN0b25lLTIwMCByb3VuZGVkLXhsIHB4LTQgcHktMyBtdC0xIiAvPjwvZGl2PgogICAgICA8ZGl2PjxsYWJlbCBjbGFzcz0idGV4dC14cyBmb250LXNlbWlib2xkIHRleHQtc3RvbmUtNTAwIj7Zhtin2YUg2K7Yp9mG2YjYp9iv2q/bjDwvbGFiZWw+PGlucHV0IGlkPSJsYXN0TmFtZUlucHV0IiBjbGFzcz0idy1mdWxsIGJvcmRlciBib3JkZXItc3RvbmUtMjAwIHJvdW5kZWQteGwgcHgtNCBweS0zIG10LTEiIC8+PC9kaXY+CiAgICAgIDxkaXY+PGxhYmVsIGNsYXNzPSJ0ZXh0LXhzIGZvbnQtc2VtaWJvbGQgdGV4dC1zdG9uZS01MDAiPtiz2YY8L2xhYmVsPjxpbnB1dCBpZD0iYWdlSW5wdXQiIHR5cGU9Im51bWJlciIgbWluPSIxNyIgbWF4PSI3NSIgY2xhc3M9InctZnVsbCBib3JkZXIgYm9yZGVyLXN0b25lLTIwMCByb3VuZGVkLXhsIHB4LTQgcHktMyBtdC0xIiAvPjwvZGl2PgogICAgICAke1ByaW1hcnlCdXR0b24oItiq2qnZhduM2YQg2KvYqNiq4oCM2YbYp9mFIiwgInN1Ym1pdFJlZ2lzdGVyIil9CiAgICA8L2Rpdj5gKX0KICA8L2Rpdj5gOwp9CgovKiA9PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT0KICAg2YbYuNix2LPZhtis24wg2KfZiNmE24zZhiDZhdix2KfYrNi52YcgKNmB2YLYtyDbjNqp4oCM2KjYp9ixKQogICA9PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT0gKi8KZnVuY3Rpb24gc2NyZWVuRG9ub3JTdXJ2ZXkoKSB7CiAgY29uc3QgZiA9IHN0YXRlLmZvcm07CiAgY29uc3QgZmlsbGVkID0gU1VSVkVZX0NBVEVHT1JJRVMuZXZlcnkoKFtrZXldKSA9PiBmW2tleV0pICYmIGYucmVmZXJyYWxTb3VyY2U7CiAgcmV0dXJuIGA8ZGl2IGNsYXNzPSJtYXgtdy1zbSBteC1hdXRvIHAtNSBwYi0xMCI+CiAgICAke1RvcEJhcigi2YbYuNix2LPZhtis24wg2KfZiNmE24zZhiDZhdix2KfYrNi52YciKX0ke0Vycm9yQm94KHN0YXRlLmVycm9yTXNnKX0KICAgICR7Q2FyZChgPGRpdiBjbGFzcz0icC01IHNwYWNlLXktNSI+CiAgICAgIDxwIGNsYXNzPSJ0ZXh0LXhzIHRleHQtc3RvbmUtNDAwIj7Yp9uM2YYg2YbYuNix2LPZhtis24wg2YHZgti3INuM2qnigIzYqNin2LHYjCDYqNix2KfbjCDYp9mI2YTbjNmGINmF2LHYp9is2LnZh+KAjNuMINi02YXYpyDYqtqp2YXbjNmEINmF24zigIzYtNmHLjwvcD4KICAgICAgJHtTVVJWRVlfQ0FURUdPUklFUy5tYXAoKFtrZXksbGFiZWxdKSA9PiBSYXRpbmdSb3cobGFiZWwsIGtleSkpLmpvaW4oIiIpfQogICAgICA8ZGl2PjxwIGNsYXNzPSJ0ZXh0LXNtIGZvbnQtc2VtaWJvbGQgdGV4dC10ZWFsLTk1MCBtYi0yIj7ahti32YjYsSDYqNinINmF2LHaqdiyINii2LTZhtinINi02K/bjNiv2J88L3A+CiAgICAgICAgPGRpdiBjbGFzcz0iZ3JpZCBncmlkLWNvbHMtMiBnYXAtMiI+JHtSRUZFUlJBTF9PUFRJT05TLm1hcCgobykgPT4gYAogICAgICAgICAgPGJ1dHRvbiBkYXRhLWFjdGlvbj0ic2V0Rm9ybSIgZGF0YS1rZXk9InJlZmVycmFsU291cmNlIiBkYXRhLXZhbHVlPSIke2VzYyhvKX0iIGNsYXNzPSJweS0yLjUgcm91bmRlZC1sZyB0ZXh0LXhzIGJvcmRlciAke2YucmVmZXJyYWxTb3VyY2U9PT1vPyJiZy10ZWFsLTgwMCB0ZXh0LXdoaXRlIGJvcmRlci10ZWFsLTgwMCI6ImJnLXdoaXRlIGJvcmRlci1zdG9uZS0yMDAgdGV4dC1zdG9uZS02MDAifSI+JHtlc2Mobyl9PC9idXR0b24+CiAgICAgICAgYCkuam9pbigiIil9PC9kaXY+CiAgICAgIDwvZGl2PgogICAgICA8ZGl2PjxwIGNsYXNzPSJ0ZXh0LXNtIGZvbnQtc2VtaWJvbGQgdGV4dC10ZWFsLTk1MCBtYi0yIj7ZvtuM2LTZhtmH2KfYryDbjNinINin2YbYqtmC2KfYryAo2KfYrtiq24zYp9ix24wpPC9wPgogICAgICAgIDx0ZXh0YXJlYSBpZD0iZnJlZVRleHRJbnB1dCIgcm93cz0iMyIgY2xhc3M9InctZnVsbCBib3JkZXIgYm9yZGVyLXN0b25lLTIwMCByb3VuZGVkLXhsIHB4LTQgcHktMyI+PC90ZXh0YXJlYT4KICAgICAgPC9kaXY+CiAgICAgICR7UHJpbWFyeUJ1dHRvbigi2KvYqNiqINmG2LjYsdiz2YbYrNuMIiwgInN1Ym1pdFN1cnZleSIsIHsgZGlzYWJsZWQ6ICFmaWxsZWQgfSl9CiAgICA8L2Rpdj5gKX0KICA8L2Rpdj5gOwp9CgpmdW5jdGlvbiBzY3JlZW5Eb25vclRlc3RQZW5kaW5nKCkgewogIHJldHVybiBgPGRpdiBjbGFzcz0ibWF4LXctc20gbXgtYXV0byBwLTUiPgogICAgJHtUb3BCYXIoItiv2LEg2KfZhtiq2LjYp9ixINmG2KrbjNis2YciLCAiZG9ub3JMb2dvdXQiKX0KICAgICR7Q2FyZChgPGRpdiBjbGFzcz0icC02IHRleHQtY2VudGVyIj4KICAgICAgPGRpdiBjbGFzcz0idy0xNCBoLTE0IHJvdW5kZWQtZnVsbCBiZy1hbWJlci0xMDAgZmxleCBpdGVtcy1jZW50ZXIganVzdGlmeS1jZW50ZXIgbXgtYXV0byBtYi00Ij48c3BhbiBjbGFzcz0idGV4dC0yeGwiPiYjOTIwMzs8L3NwYW4+PC9kaXY+CiAgICAgIDxwIGNsYXNzPSJ0ZXh0LXNtIHRleHQtc3RvbmUtNjAwIGxlYWRpbmctNyI+2KfYsiDYq9io2Kog2YbYuNixINi02YXYpyDYs9m+2KfYs9qv2LLYp9ix24zZhS4g2YbYqtin24zYrCDYotiy2YXYp9uM2LTigIzZh9in24wg2LTZhdinINm+2LMg2KfYsiDYrdiv2YjYryDbtyDYqtinINux27Ag2LHZiNiyINii2YXYp9iv2Ycg2K7ZiNin2YfYryDYtNivLiDZvtizINin2LIg2KrYo9uM24zYr9iMINm+2YbZhCDYtNmF2Kcg2YHYudin2YQg2LTYr9mHINmIINin2YXaqdin2YYg2KrYuduM24zZhiDYstmF2KfZhiDZhdix2KfYrNi52Ycg2KjYsdin24wg2KfZiNmE24zZhiDYp9mH2K/YpyDZgdix2KfZh9mFINmF24zigIzYtNmI2K8uINmG2KrbjNis2Ycg2KfYsiDYt9ix24zZgiDZvtuM2KfZhdqpINmG24zYsiDYp9i32YTYp9i54oCM2LHYs9in2YbbjCDYrtmI2KfZh9ivINi02K8uPC9wPgogICAgPC9kaXY+YCl9CiAgICAke05vdGlmaWNhdGlvbnNMaXN0KCl9CiAgPC9kaXY+YDsKfQoKZnVuY3Rpb24gTm90aWZpY2F0aW9uc0xpc3QoKSB7CiAgaWYgKCFzdGF0ZS5kb25vck5vdGlmaWNhdGlvbnMgfHwgc3RhdGUuZG9ub3JOb3RpZmljYXRpb25zLmxlbmd0aCA9PT0gMCkgcmV0dXJuICIiOwogIGNvbnN0IGxhdGVzdCA9IHN0YXRlLmRvbm9yTm90aWZpY2F0aW9uc1swXTsKICByZXR1cm4gYDxkaXYgY2xhc3M9Im10LTQiPiR7Q2FyZChgPGRpdiBjbGFzcz0icC00IGJnLXRlYWwtNTAgYm9yZGVyLXRlYWwtMjAwIj4KICAgIDxkaXYgY2xhc3M9ImZsZXggaXRlbXMtY2VudGVyIGdhcC0yIG1iLTIgdGV4dC10ZWFsLTgwMCBmb250LWJvbGQgdGV4dC1zbSI+JiMxMjgxNzI7INii2K7YsduM2YYg2b7bjNin2YU8L2Rpdj4KICAgIDxwIGNsYXNzPSJ0ZXh0LXNtIHRleHQtc3RvbmUtNzAwIj4ke2VzYyhsYXRlc3QudGV4dCl9PC9wPgogICAgPHAgY2xhc3M9InRleHQteHMgdGV4dC1zdG9uZS00MDAgbXQtMiI+JHtmbXREYXRlU2hvcnQobGF0ZXN0LmNyZWF0ZWRBdCl9PC9wPgogIDwvZGl2PmApfTwvZGl2PmA7Cn0KCi8qID09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PQogICDYrtin2YbZh+KAjNuMINin2YfYr9in2qnZhtmG2K/ZhwogICA9PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT0gKi8KZnVuY3Rpb24gc2NyZWVuRG9ub3JIb21lKCkgewogIGNvbnN0IGQgPSBzdGF0ZS5kb25vcjsKICBpZiAoIWQpIHJldHVybiBgPGRpdiBjbGFzcz0icC0xMCB0ZXh0LWNlbnRlciB0ZXh0LXN0b25lLTQwMCI+2K/YsSDYrdin2YQg2KjYp9ix2q/YsNin2LHbjC4uLjwvZGl2PmA7CiAgY29uc3QgYXBwdCA9IGQuY3VycmVudEFwcG9pbnRtZW50OwogIHJldHVybiBgPGRpdiBjbGFzcz0ibWF4LXctc20gbXgtYXV0byBwLTUgcGItMTAiPgogICAgPGRpdiBjbGFzcz0iZmxleCBpdGVtcy1jZW50ZXIganVzdGlmeS1iZXR3ZWVuIG1iLTUiPgogICAgICA8YnV0dG9uIGRhdGEtYWN0aW9uPSJkb25vckxvZ291dCIgY2xhc3M9InctOSBoLTkgcm91bmRlZC1mdWxsIGZsZXggaXRlbXMtY2VudGVyIGp1c3RpZnktY2VudGVyIHRleHQtc3RvbmUtNTAwIGJnLXdoaXRlIGJvcmRlciBib3JkZXItc3RvbmUtMjAwIHNoYWRvdy1zbSBob3ZlcjpiZy1zdG9uZS01MCI+JHtJY29uKCJsb2ctb3V0Iiwidy00IGgtNCIpfTwvYnV0dG9uPgogICAgICA8ZGl2IGNsYXNzPSJmbGV4IGl0ZW1zLWNlbnRlciBnYXAtMi41Ij4KICAgICAgICA8ZGl2IGNsYXNzPSJ0ZXh0LXJpZ2h0Ij48cCBjbGFzcz0idGV4dC14cyB0ZXh0LXN0b25lLTQwMCI+2K7ZiNi0INin2YjZhdiv24w8L3A+PHAgY2xhc3M9ImZvbnQtYm9sZCB0ZXh0LXRlYWwtOTUwIj4ke2VzYyhkLmZpcnN0TmFtZSl9ICR7ZXNjKGQubGFzdE5hbWUpfTwvcD48L2Rpdj4KICAgICAgICA8ZGl2IGNsYXNzPSJ3LTEwIGgtMTAgcm91bmRlZC1mdWxsIGJnLWdyYWRpZW50LXRvLWJyIGZyb20tdGVhbC03MDAgdG8tdGVhbC05MDAgdGV4dC13aGl0ZSBmbGV4IGl0ZW1zLWNlbnRlciBqdXN0aWZ5LWNlbnRlciBmb250LWJvbGQgc2hhZG93LW1kIHNoYWRvdy10ZWFsLTkwMC8yMCI+JHtlc2MoZC5maXJzdE5hbWUuY2hhckF0KDApKX08L2Rpdj4KICAgICAgPC9kaXY+CiAgICA8L2Rpdj4KICAgICR7VG9hc3Qoc3RhdGUudG9hc3QpfSR7RXJyb3JCb3goc3RhdGUuZXJyb3JNc2cpfQoKICAgICR7Q2FyZChgPGRpdiBjbGFzcz0icC00IGZsZXggaXRlbXMtY2VudGVyIGdhcC0zIj4KICAgICAgPHNwYW4gY2xhc3M9InRleHQtMnhsIj4mIzg1MDU7JiM2NTAzOTs8L3NwYW4+CiAgICAgIDxkaXY+PHAgY2xhc3M9ImZvbnQtYm9sZCB0ZXh0LXRlYWwtOTUwIj4ke1NUQVRVU19MQUJFTFNbZC5zdGF0dXNdIHx8IGQuc3RhdHVzfTwvcD4KICAgICAgPHAgY2xhc3M9InRleHQteHMgdGV4dC1zdG9uZS01MDAiPiR7ZC5hcHBvaW50bWVudHMuZmlsdGVyKGE9PmEuZG9uYXRlZD09PXRydWUpLmxlbmd0aCA/IGDYqtinINin2YTYp9mGICR7ZmFEaWdpdHMoZC5hcHBvaW50bWVudHMuZmlsdGVyKGE9PmEuZG9uYXRlZD09PXRydWUpLmxlbmd0aCl9INio2KfYsSDYp9mH2K/YpyDaqdix2K/bjNivYCA6ICLZh9mG2YjYsiDYp9mH2K/Yp9uM24wg2KvYqNiqINmG2LTYr9mHIn08L3A+PC9kaXY+CiAgICA8L2Rpdj5gLCAibWItNCIpfQoKICAgICR7Tm90aWZpY2F0aW9uc0xpc3QoKX0KCiAgICAke2FwcHQgPyBBcHBvaW50bWVudENhcmQoYXBwdCkgOiAoCiAgICAgIGQuZWxpZ2libGVGb3JCb29raW5nID8gQ2FyZChgPGRpdiBjbGFzcz0icC00Ij4KICAgICAgICA8cCBjbGFzcz0iZm9udC1ib2xkIHRleHQtdGVhbC05NTAgbWItMyI+2YXbjOKAjNiq2YjZhtuM2K8g2YbZiNio2Kog2KfZh9iv2Kcg2LHYstix2Ygg2qnZhtuM2K88L3A+CiAgICAgICAgJHtQcmltYXJ5QnV0dG9uKCLYsdiy2LHZiCDZhtmI2KjYqiIsICJnb0Jvb2tBcHBvaW50bWVudCIpfQogICAgICA8L2Rpdj5gLCAibWItNCBiZy1lbWVyYWxkLTUwIGJvcmRlci1lbWVyYWxkLTIwMCIpIDoKICAgICAgZC5uZXh0RWxpZ2libGVEYXRlID8gQ2FyZChgPGRpdiBjbGFzcz0icC00Ij48cCBjbGFzcz0idGV4dC1zbSB0ZXh0LXN0b25lLTYwMCI+2YbZiNio2Kog2KjYudiv24wg2KfYsiDYqtin2LHbjNiuIDxiPiR7Zm10RGF0ZShkLm5leHRFbGlnaWJsZURhdGUpfTwvYj4g2YLYp9io2YQg2LHYstix2YjZhy48L3A+PC9kaXY+YCwgIm1iLTQiKSA6ICIiCiAgICApfQoKICAgICR7KGQucGVuZGluZ0ZvbGxvd1VwcyAmJiBkLnBlbmRpbmdGb2xsb3dVcHMubGVuZ3RoID4gMCkgPyBDYXJkKGA8ZGl2IGNsYXNzPSJwLTQiPgogICAgICA8ZGl2IGNsYXNzPSJmbGV4IGl0ZW1zLWNlbnRlciBnYXAtMyBtYi0zIj48c3BhbiBjbGFzcz0idGV4dC0yeGwiPiYjMTI4MjAyOzwvc3Bhbj4KICAgICAgICA8ZGl2PjxwIGNsYXNzPSJmb250LWJvbGQgdGV4dC10ZWFsLTk1MCI+2b7bjNqv24zYsduMINm+2LMg2KfYsiDYp9mH2K/YpzwvcD48cCBjbGFzcz0idGV4dC14cyB0ZXh0LXN0b25lLTUwMCI+2YTYt9mB2KfZiyDZiNi22LnbjNiqINiz2YTYp9mF2KrYqtmI2YYg2LHZiCDYq9io2Kog2qnZhtuM2K8gKNix2YjYsiAke2ZhRGlnaXRzKGQucGVuZGluZ0ZvbGxvd1Vwc1swXS5kYXlJbmRleCl9KTwvcD48L2Rpdj4KICAgICAgPC9kaXY+CiAgICAgICR7UHJpbWFyeUJ1dHRvbigi2KraqdmF24zZhCDZgdix2YUg2b7bjNqv24zYsduMIiwgIm9wZW5Gb2xsb3dVcCIsIHsgZGF0YTogeyBhcHB0OiBkLnBlbmRpbmdGb2xsb3dVcHNbMF0uYXBwb2ludG1lbnRJZCwgZGF5OiBkLnBlbmRpbmdGb2xsb3dVcHNbMF0uZGF5SW5kZXggfSB9KX0KICAgIDwvZGl2PmAsICJtYi00IGJnLWFtYmVyLTUwIGJvcmRlci1hbWJlci0yMDAiKSA6ICIifQoKICAgIDxwIGNsYXNzPSJ0ZXh0LXhzIGZvbnQtYm9sZCB0ZXh0LXN0b25lLTQwMCBtYi0yIj7Yqtin2LHbjNiu2obZh+KAjNuMINmG2YjYqNiq4oCM2YfYpzwvcD4KICAgIDxkaXYgY2xhc3M9InNwYWNlLXktMiI+CiAgICAgICR7ZC5hcHBvaW50bWVudHMubGVuZ3RoPT09MCA/IGA8cCBjbGFzcz0idGV4dC1zbSB0ZXh0LXN0b25lLTQwMCB0ZXh0LWNlbnRlciBweS02Ij7Zh9mG2YjYsiDZhtmI2KjYqtuMINir2KjYqiDZhti02K/ZhzwvcD5gIDogWy4uLmQuYXBwb2ludG1lbnRzXS5zb3J0KChhLGIpPT5uZXcgRGF0ZShiLmNyZWF0ZWRBdCktbmV3IERhdGUoYS5jcmVhdGVkQXQpKS5tYXAoKGEpID0+IGAKICAgICAgICAke0NhcmQoYDxkaXYgY2xhc3M9InAtMy41IGZsZXggaXRlbXMtY2VudGVyIGp1c3RpZnktYmV0d2VlbiI+CiAgICAgICAgICA8ZGl2PjxwIGNsYXNzPSJ0ZXh0LXNtIGZvbnQtc2VtaWJvbGQgdGV4dC10ZWFsLTk1MCI+JHtmbXREYXRlVGltZShhLmNvbmZpcm1lZERhdGV8fGEucmVxdWVzdGVkRGF0ZSl9PC9wPgogICAgICAgICAgPHAgY2xhc3M9InRleHQteHMgdGV4dC1zdG9uZS00MDAiPiR7YS5zdGF0dXM9PT0iY2FuY2VsbGVkIj8i2YTYutmI2LTYr9mHIjphLmRvbmF0ZWQ9PT10cnVlPyLYp9mH2K/YpyDYp9mG2KzYp9mFINi02K8iOmEuZG9uYXRlZD09PWZhbHNlPyLYp9mH2K/YpyDYp9mG2KzYp9mFINmG2LTYryI6YS5zdGF0dXM9PT0iY29uZmlybWVkIj8i2KrYp9uM24zYr9i02K/ZhyI6YS5zdGF0dXM9PT0icmVxdWVzdGVkIj8i2K/YsSDYp9mG2KrYuNin2LEg2KrYp9uM24zYryI6YS5zdGF0dXN9PC9wPjwvZGl2PgogICAgICAgIDwvZGl2PmApfQogICAgICBgKS5qb2luKCIiKX0KICAgIDwvZGl2PgogIDwvZGl2PmA7Cn0KCmZ1bmN0aW9uIEFwcG9pbnRtZW50Q2FyZChhcHB0KSB7CiAgaWYgKGFwcHQuc3RhdHVzID09PSAicmVxdWVzdGVkIikgewogICAgcmV0dXJuIENhcmQoYDxkaXYgY2xhc3M9InAtNCI+PHAgY2xhc3M9ImZvbnQtYm9sZCB0ZXh0LXRlYWwtOTUwIG1iLTEiPtiv2LHYrtmI2KfYs9iqINmG2YjYqNiqINi02YXYpyDYq9io2Kog2LTYrzwvcD4KICAgICAgPHAgY2xhc3M9InRleHQteHMgdGV4dC1zdG9uZS01MDAgbWItMyI+2LLZhdin2YYg2K/Ysdiu2YjYp9iz2KrbjDogJHtmbXREYXRlVGltZShhcHB0LnJlcXVlc3RlZERhdGUpfSDigJQg2YXZhtiq2LjYsSDYqtin24zbjNivINmF2K/bjNixINio2KfYtNuM2K8uPC9wPgogICAgICAke1NtYWxsQnV0dG9uKCLZhNi62Ygg2K/Ysdiu2YjYp9iz2KoiLCAiY2FuY2VsQXBwb2ludG1lbnQiLCB7IGRhdGE6IHsgaWQ6IGFwcHQuaWQgfSwgdG9uZTogInJvc2UiIH0pfQogICAgPC9kaXY+YCwgIm1iLTQgYmctYW1iZXItNTAgYm9yZGVyLWFtYmVyLTIwMCIpOwogIH0KICBpZiAoYXBwdC5zdGF0dXMgPT09ICJyZXNjaGVkdWxlZF9ieV9hZG1pbiIpIHsKICAgIHJldHVybiBDYXJkKGA8ZGl2IGNsYXNzPSJwLTQiPjxwIGNsYXNzPSJmb250LWJvbGQgdGV4dC10ZWFsLTk1MCBtYi0xIj7YstmF2KfZhiDZvtuM2LTZhtmH2KfYr9uMINis2K/bjNivPC9wPgogICAgICA8cCBjbGFzcz0idGV4dC1zbSB0ZXh0LXN0b25lLTYwMCBtYi0zIj4ke2ZtdERhdGVUaW1lKGFwcHQuY29uZmlybWVkRGF0ZSl9JHthcHB0LmFkbWluTm90ZSA/ICIg4oCUICIgKyBlc2MoYXBwdC5hZG1pbk5vdGUpIDogIiJ9PC9wPgogICAgICA8ZGl2IGNsYXNzPSJncmlkIGdyaWQtY29scy0yIGdhcC0yIj4KICAgICAgICAke1NtYWxsQnV0dG9uKCLZgtio2YjZhCDYr9in2LHZhSIsICJhY2NlcHRSZXNjaGVkdWxlIiwgeyBkYXRhOiB7IGlkOiBhcHB0LmlkIH0sIHRvbmU6ICJlbWVyYWxkIiB9KX0KICAgICAgICAke1NtYWxsQnV0dG9uKCLZhNi62Ygg2YbZiNio2KoiLCAiY2FuY2VsQXBwb2ludG1lbnQiLCB7IGRhdGE6IHsgaWQ6IGFwcHQuaWQgfSwgdG9uZTogInJvc2UiIH0pfQogICAgICA8L2Rpdj4KICAgIDwvZGl2PmAsICJtYi00IGJnLWFtYmVyLTUwIGJvcmRlci1hbWJlci0yMDAiKTsKICB9CiAgcmV0dXJuIENhcmQoYDxkaXYgY2xhc3M9InAtNCI+PHAgY2xhc3M9ImZvbnQtYm9sZCB0ZXh0LXRlYWwtOTUwIG1iLTEiPtmG2YjYqNiqINi02YXYpyDYqtin24zbjNivINi02K/ZhzwvcD4KICAgIDxwIGNsYXNzPSJ0ZXh0LXNtIHRleHQtc3RvbmUtNjAwIG1iLTMiPiR7Zm10RGF0ZVRpbWUoYXBwdC5jb25maXJtZWREYXRlKX08L3A+CiAgICAke1NtYWxsQnV0dG9uKCLZhNi62Ygg2YbZiNio2KoiLCAiY2FuY2VsQXBwb2ludG1lbnQiLCB7IGRhdGE6IHsgaWQ6IGFwcHQuaWQgfSwgdG9uZTogInJvc2UiIH0pfQogIDwvZGl2PmAsICJtYi00IGJnLWVtZXJhbGQtNTAgYm9yZGVyLWVtZXJhbGQtMjAwIik7Cn0KCmZ1bmN0aW9uIHNjcmVlbkRvbm9yQm9vaygpIHsKICBjb25zdCBkYXRlID0gc3RhdGUuZm9ybS5ib29rRGF0ZSB8fCB0b2RheUlTT0RhdGUoKTsKICBjb25zdCBzbG90cyA9IHN0YXRlLmZvcm0uc2xvdHMgfHwgW107CiAgY29uc3QgbW9kZSA9IHN0YXRlLmZvcm0uYXBwb2ludG1lbnRNb2RlIHx8ICJhdXRvIjsKICByZXR1cm4gYDxkaXYgY2xhc3M9Im1heC13LXNtIG14LWF1dG8gcC01Ij4KICAgICR7VG9wQmFyKCLYsdiy2LHZiCDZhtmI2KjYqiDYp9mH2K/YpyIsICJiYWNrVG9Eb25vckhvbWUiKX0ke0Vycm9yQm94KHN0YXRlLmVycm9yTXNnKX0KICAgICR7Q2FyZChgPGRpdiBjbGFzcz0icC01Ij4KICAgICAgPGxhYmVsIGNsYXNzPSJ0ZXh0LXhzIGZvbnQtc2VtaWJvbGQgdGV4dC1zdG9uZS01MDAiPtiq2KfYsduM2K4g2YXZiNix2K8g2YbYuNixPC9sYWJlbD4KICAgICAgPGlucHV0IGlkPSJib29rRGF0ZUlucHV0IiB0eXBlPSJkYXRlIiB2YWx1ZT0iJHtkYXRlfSIgY2xhc3M9InctZnVsbCBib3JkZXIgYm9yZGVyLXN0b25lLTIwMCByb3VuZGVkLXhsIHB4LTQgcHktMyBtdC0xIG1iLTMiIC8+CiAgICAgICR7bW9kZSA9PT0gImF1dG8iID8gYAogICAgICAgICR7U21hbGxCdXR0b24oItmG2YXYp9uM2LQg2LPYp9i52KrigIzZh9in24wg2K7Yp9mE24wiLCAibG9hZFNsb3RzIiwgeyB0b25lOiAic3RvbmUiIH0pfQogICAgICAgIDxkaXYgY2xhc3M9ImdyaWQgZ3JpZC1jb2xzLTMgZ2FwLTIgbXQtMyI+CiAgICAgICAgICAke3Nsb3RzLm1hcCgocykgPT4gYDxidXR0b24gZGF0YS1hY3Rpb249InBpY2tTbG90IiBkYXRhLXRpbWU9IiR7cy50aW1lfSIgJHshcy5hdmFpbGFibGU/ImRpc2FibGVkIjoiIn0KICAgICAgICAgICAgY2xhc3M9InB5LTIuNSByb3VuZGVkLWxnIHRleHQtc20gYm9yZGVyICR7c3RhdGUuZm9ybS5waWNrZWRUaW1lPT09cy50aW1lPyJiZy10ZWFsLTgwMCB0ZXh0LXdoaXRlIGJvcmRlci10ZWFsLTgwMCI6ImJnLXdoaXRlIGJvcmRlci1zdG9uZS0yMDAgdGV4dC1zdG9uZS02MDAifSBkaXNhYmxlZDpvcGFjaXR5LTMwIj4ke3MudGltZX08L2J1dHRvbj5gKS5qb2luKCIiKX0KICAgICAgICA8L2Rpdj4KICAgICAgICA8ZGl2IGNsYXNzPSJtdC00Ij4ke1ByaW1hcnlCdXR0b24oItir2KjYqiDZhtmI2KjYqiIsICJzdWJtaXRCb29raW5nIiwgeyBkaXNhYmxlZDogIXN0YXRlLmZvcm0ucGlja2VkVGltZSB9KX08L2Rpdj4KICAgICAgYCA6IGAKICAgICAgICA8bGFiZWwgY2xhc3M9InRleHQteHMgZm9udC1zZW1pYm9sZCB0ZXh0LXN0b25lLTUwMCI+2LPYp9i52Kog2b7bjNi02YbZh9in2K/bjDwvbGFiZWw+CiAgICAgICAgPGlucHV0IGlkPSJib29rVGltZUlucHV0IiB0eXBlPSJ0aW1lIiBjbGFzcz0idy1mdWxsIGJvcmRlciBib3JkZXItc3RvbmUtMjAwIHJvdW5kZWQteGwgcHgtNCBweS0zIG10LTEgbWItMyIgLz4KICAgICAgICA8bGFiZWwgY2xhc3M9InRleHQteHMgZm9udC1zZW1pYm9sZCB0ZXh0LXN0b25lLTUwMCI+2KrZiNi224zYrSAo2KfYrtiq24zYp9ix24wpPC9sYWJlbD4KICAgICAgICA8dGV4dGFyZWEgaWQ9ImJvb2tOb3RlSW5wdXQiIHJvd3M9IjIiIGNsYXNzPSJ3LWZ1bGwgYm9yZGVyIGJvcmRlci1zdG9uZS0yMDAgcm91bmRlZC14bCBweC00IHB5LTMgbXQtMSBtYi0zIj48L3RleHRhcmVhPgogICAgICAgIDxkaXYgY2xhc3M9Im10LTIiPiR7UHJpbWFyeUJ1dHRvbigi2KvYqNiqINiv2LHYrtmI2KfYs9iqINmG2YjYqNiqIiwgInN1Ym1pdEJvb2tpbmciKX08L2Rpdj4KICAgICAgYH0KICAgIDwvZGl2PmApfQogIDwvZGl2PmA7Cn0KCmZ1bmN0aW9uIHNjcmVlbkRvbm9yRm9sbG93VXAoKSB7CiAgY29uc3QgZiA9IHN0YXRlLmZvcm07CiAgY29uc3QgY29tcGxldGUgPSBmLmdlbmVyYWxDb25kaXRpb24gJiYgZi5kaXp6aW5lc3MgIT09IHVuZGVmaW5lZCAmJiBmLmluamVjdGlvblNpdGVJc3N1ZSAhPT0gdW5kZWZpbmVkICYmIGYuc2F0aXNmaWVkICE9PSB1bmRlZmluZWQgJiYgZi5yZWFkeUZvck5leHQgIT09IHVuZGVmaW5lZDsKICByZXR1cm4gYDxkaXYgY2xhc3M9Im1heC13LXNtIG14LWF1dG8gcC01Ij4KICAgICR7VG9wQmFyKCLZvtuM2q/bjNix24wg2b7YsyDYp9iyINin2YfYr9inIil9JHtFcnJvckJveChzdGF0ZS5lcnJvck1zZyl9CiAgICAke0NhcmQoYDxkaXYgY2xhc3M9InAtNSBzcGFjZS15LTUiPgogICAgICA8ZGl2PjxwIGNsYXNzPSJ0ZXh0LXNtIGZvbnQtc2VtaWJvbGQgdGV4dC10ZWFsLTk1MCBtYi0yIj7ZiNi22LnbjNiqINi52YXZiNmF24wg2LTZhdinINqG2q/ZiNmG2Ycg2KfYs9iq2J88L3A+CiAgICAgICAgPGRpdiBjbGFzcz0iZ3JpZCBncmlkLWNvbHMtMyBnYXAtMiI+JHtbItiu2YjYqCIsItmF2KrZiNiz2LciLCLYtti524zZgSJdLm1hcCgobyk9PmAKICAgICAgICAgIDxidXR0b24gZGF0YS1hY3Rpb249InNldEZvcm0iIGRhdGEta2V5PSJnZW5lcmFsQ29uZGl0aW9uIiBkYXRhLXZhbHVlPSIke299IiBjbGFzcz0icHktMyByb3VuZGVkLWxnIHRleHQtc20gYm9yZGVyICR7Zi5nZW5lcmFsQ29uZGl0aW9uPT09bz8iYmctdGVhbC04MDAgdGV4dC13aGl0ZSBib3JkZXItdGVhbC04MDAiOiJiZy13aGl0ZSBib3JkZXItc3RvbmUtMjAwIHRleHQtc3RvbmUtNjAwIn0iPiR7b308L2J1dHRvbj4KICAgICAgICBgKS5qb2luKCIiKX08L2Rpdj4KICAgICAgPC9kaXY+CiAgICAgICR7WWVzTm9Sb3coItii24zYpyDYp9it2LPYp9izINiz2LHar9uM2KzZhyDYr9in2LTYqtmH4oCM2KfbjNiv2J8iLCAiZGl6emluZXNzIil9CiAgICAgICR7WWVzTm9Sb3coItii24zYpyDZhdit2YQg2KrYstix24zZgiDZhdi02qnZhNuMINiv2KfYsdiv2J8iLCAiaW5qZWN0aW9uU2l0ZUlzc3VlIil9CiAgICAgICR7WWVzTm9Sb3coItii24zYpyDYp9iyINix2YjZhtivINin2YfYr9inINix2LbYp9uM2Kog2K/Yp9i02KrbjNiv2J8iLCAic2F0aXNmaWVkIil9CiAgICAgICR7WWVzTm9Sb3coItii24zYpyDYqNix2KfbjCDZhdix2KfYrNi52YfigIzbjCDYqNi52K/bjCDYotmF2KfYr9mH4oCM2KfbjNiv2J8iLCAicmVhZHlGb3JOZXh0Iil9CiAgICAgIDxkaXY+PGxhYmVsIGNsYXNzPSJmbGV4IGl0ZW1zLWNlbnRlciBnYXAtMiB0ZXh0LXNtIHRleHQtc3RvbmUtNjAwIj4KICAgICAgICA8aW5wdXQgdHlwZT0iY2hlY2tib3giIGRhdGEtYWN0aW9uPSJ0b2dnbGVDYWxsYmFjayIgJHtmLmNhbGxiYWNrUmVxdWVzdGVkPyJjaGVja2VkIjoiIn0gLz4g2YXbjOKAjNiu2YjYp9mFINio2KfZh9in2YUg2KrZhdin2LMg2Kjar9uM2LHbjNivCiAgICAgIDwvbGFiZWw+PC9kaXY+CiAgICAgIDxkaXY+PHAgY2xhc3M9InRleHQtc20gZm9udC1zZW1pYm9sZCB0ZXh0LXRlYWwtOTUwIG1iLTIiPtiq2YjYttuM2K0g2KraqdmF24zZhNuMICjYp9iu2KrbjNin2LHbjCk8L3A+CiAgICAgICAgPHRleHRhcmVhIGlkPSJmb2xsb3d1cE5vdGVzIiByb3dzPSIyIiBjbGFzcz0idy1mdWxsIGJvcmRlciBib3JkZXItc3RvbmUtMjAwIHJvdW5kZWQteGwgcHgtNCBweS0zIj48L3RleHRhcmVhPgogICAgICA8L2Rpdj4KICAgICAgJHtQcmltYXJ5QnV0dG9uKCLYq9io2Kog2b7bjNqv24zYsduMIiwgInN1Ym1pdEZvbGxvd1VwIiwgeyBkaXNhYmxlZDogIWNvbXBsZXRlIH0pfQogICAgPC9kaXY+YCl9CiAgPC9kaXY+YDsKfQpmdW5jdGlvbiBZZXNOb1JvdyhsYWJlbCwga2V5KSB7CiAgY29uc3QgdiA9IHN0YXRlLmZvcm1ba2V5XTsKICByZXR1cm4gYDxkaXY+PHAgY2xhc3M9InRleHQtc20gdGV4dC1zdG9uZS03MDAgbWItMiI+JHtlc2MobGFiZWwpfTwvcD4KICAgIDxkaXYgY2xhc3M9ImZsZXggZ2FwLTMiPgogICAgICA8YnV0dG9uIGRhdGEtYWN0aW9uPSJzZXRGb3JtIiBkYXRhLWtleT0iJHtrZXl9IiBkYXRhLXZhbHVlPSJ0cnVlIiBjbGFzcz0iZmxleC0xIHB5LTIuNSByb3VuZGVkLWxnIGZvbnQtc2VtaWJvbGQgYm9yZGVyICR7dj09PXRydWU/ImJnLXJvc2UtNjAwIHRleHQtd2hpdGUgYm9yZGVyLXJvc2UtNjAwIjoiYmctd2hpdGUgdGV4dC1zdG9uZS01MDAgYm9yZGVyLXN0b25lLTIwMCJ9Ij7YqNmE2Yc8L2J1dHRvbj4KICAgICAgPGJ1dHRvbiBkYXRhLWFjdGlvbj0ic2V0Rm9ybSIgZGF0YS1rZXk9IiR7a2V5fSIgZGF0YS12YWx1ZT0iZmFsc2UiIGNsYXNzPSJmbGV4LTEgcHktMi41IHJvdW5kZWQtbGcgZm9udC1zZW1pYm9sZCBib3JkZXIgJHt2PT09ZmFsc2U/ImJnLWVtZXJhbGQtNjAwIHRleHQtd2hpdGUgYm9yZGVyLWVtZXJhbGQtNjAwIjoiYmctd2hpdGUgdGV4dC1zdG9uZS01MDAgYm9yZGVyLXN0b25lLTIwMCJ9Ij7YrtuM2LE8L2J1dHRvbj4KICAgIDwvZGl2PgogIDwvZGl2PmA7Cn0KCi8qID09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PQogICDZhdiz24zYsSDaqdin2LHaqdmG2KfZhjog2YjYsdmI2K8g2Ygg2KrYutuM24zYsSDYsdmF2LIKICAgPT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09ICovCmZ1bmN0aW9uIHNjcmVlblN0YWZmTG9naW4oKSB7CiAgcmV0dXJuIGA8ZGl2IGNsYXNzPSJtYXgtdy1zbSBteC1hdXRvIHAtNSI+CiAgICAke1RvcEJhcigi2YjYsdmI2K8g2qnYp9ix2qnZhtin2YYiLCAiZ29MYW5kaW5nIil9JHtFcnJvckJveChzdGF0ZS5lcnJvck1zZyl9CiAgICAke0NhcmQoYDxkaXYgY2xhc3M9InAtNSBzcGFjZS15LTMiPgogICAgICA8ZGl2PjxsYWJlbCBjbGFzcz0idGV4dC14cyBmb250LXNlbWlib2xkIHRleHQtc3RvbmUtNTAwIj7Zhtin2YUg2qnYp9ix2KjYsduMPC9sYWJlbD48aW5wdXQgaWQ9InN0YWZmVXNlcm5hbWUiIGNsYXNzPSJ3LWZ1bGwgYm9yZGVyIGJvcmRlci1zdG9uZS0yMDAgcm91bmRlZC14bCBweC00IHB5LTMgbXQtMSIgLz48L2Rpdj4KICAgICAgPGRpdj48bGFiZWwgY2xhc3M9InRleHQteHMgZm9udC1zZW1pYm9sZCB0ZXh0LXN0b25lLTUwMCI+2LHZhdiyINi52KjZiNixPC9sYWJlbD48aW5wdXQgdHlwZT0icGFzc3dvcmQiIGlkPSJzdGFmZlBhc3N3b3JkIiBjbGFzcz0idy1mdWxsIGJvcmRlciBib3JkZXItc3RvbmUtMjAwIHJvdW5kZWQteGwgcHgtNCBweS0zIG10LTEiIC8+PC9kaXY+CiAgICAgICR7UHJpbWFyeUJ1dHRvbigi2YjYsdmI2K8iLCAic3RhZmZMb2dpblN1Ym1pdCIpfQogICAgICA8cCBjbGFzcz0idGV4dC14cyB0ZXh0LXN0b25lLTQwMCB0ZXh0LWNlbnRlciBwdC0yIj7Yp9mI2YTbjNmGINio2KfYsdifINmG2KfZhSDaqdin2LHYqNix24wgwqthZG1pbsK7INmIINix2YXYsiDCq2FkbWluMTIzNMK7IOKAlCDYqNmE2KfZgdin2LXZhNmHINio2LnYryDYp9iyINmI2LHZiNivINi52YjYtti0INqp2YbbjNivLjwvcD4KICAgIDwvZGl2PmApfQogIDwvZGl2PmA7Cn0KCmZ1bmN0aW9uIHNjcmVlbkNoYW5nZVBhc3N3b3JkKCkgewogIHJldHVybiBgPGRpdiBjbGFzcz0ibWF4LXctc20gbXgtYXV0byBwLTUiPgogICAgJHtUb3BCYXIoItiq2LrbjNuM2LEg2LHZhdiyINi52KjZiNixIiwgc3RhdGUuZm9yY2VkUHdDaGFuZ2UgPyBudWxsIDogImdvU3RhZmZEYXNoYm9hcmQiKX0KICAgICR7c3RhdGUuZm9yY2VkUHdDaGFuZ2UgPyBgPGRpdiBjbGFzcz0ibWItNCBwLTMgcm91bmRlZC14bCB0ZXh0LXNtIGJnLWFtYmVyLTEwMCB0ZXh0LWFtYmVyLTgwMCB0ZXh0LWNlbnRlciI+2KjYsdin24wg2KfZhdmG24zYqiDYrdiz2KfYqOKAjNiq2YjZhtiMINmE2LfZgdin2Ysg2YfZhduM2YYg2KfZhNin2YYg2LHZhdiyINix2Ygg2LnZiNi2INqp2YbbjNivLjwvZGl2PmAgOiAiIn0KICAgICR7RXJyb3JCb3goc3RhdGUuZXJyb3JNc2cpfQogICAgJHtDYXJkKGA8ZGl2IGNsYXNzPSJwLTUgc3BhY2UteS0zIj4KICAgICAgPGRpdj48bGFiZWwgY2xhc3M9InRleHQteHMgZm9udC1zZW1pYm9sZCB0ZXh0LXN0b25lLTUwMCI+2LHZhdiyINmB2LnZhNuMPC9sYWJlbD48aW5wdXQgdHlwZT0icGFzc3dvcmQiIGlkPSJjdXJQYXNzIiBjbGFzcz0idy1mdWxsIGJvcmRlciBib3JkZXItc3RvbmUtMjAwIHJvdW5kZWQteGwgcHgtNCBweS0zIG10LTEiIC8+PC9kaXY+CiAgICAgIDxkaXY+PGxhYmVsIGNsYXNzPSJ0ZXh0LXhzIGZvbnQtc2VtaWJvbGQgdGV4dC1zdG9uZS01MDAiPtix2YXYsiDYrNiv24zYryAo2K3Yr9in2YLZhCDbtiDaqdin2LHYp9qp2KrYsSk8L2xhYmVsPjxpbnB1dCB0eXBlPSJwYXNzd29yZCIgaWQ9Im5ld1Bhc3MiIGNsYXNzPSJ3LWZ1bGwgYm9yZGVyIGJvcmRlci1zdG9uZS0yMDAgcm91bmRlZC14bCBweC00IHB5LTMgbXQtMSIgLz48L2Rpdj4KICAgICAgJHtQcmltYXJ5QnV0dG9uKCLYq9io2Kog2LHZhdiyINis2K/bjNivIiwgInN1Ym1pdENoYW5nZVBhc3N3b3JkIil9CiAgICA8L2Rpdj5gKX0KICA8L2Rpdj5gOwp9CgovKiA9PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT0KICAg2K/Yp9i02KjZiNix2K8g2qnYp9ix2qnZhtin2YYKICAgPT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09ICovCmZ1bmN0aW9uIE5hdlRpbGUoaWNvbiwgbGFiZWwsIGFjdGlvbikgewogIHJldHVybiBgPGJ1dHRvbiBkYXRhLWFjdGlvbj0iJHthY3Rpb259IiBjbGFzcz0iZmxleCBmbGV4LWNvbCBpdGVtcy1jZW50ZXIganVzdGlmeS1jZW50ZXIgZ2FwLTIgcC00IGJnLXdoaXRlIHJvdW5kZWQtMnhsIGJvcmRlciBib3JkZXItc3RvbmUtMjAwLzcwIHNoYWRvdy1zbSBob3ZlcjpzaGFkb3ctbWQgaG92ZXI6LXRyYW5zbGF0ZS15LTAuNSB0cmFuc2l0aW9uLWFsbCI+CiAgICA8ZGl2IGNsYXNzPSJ3LTEwIGgtMTAgcm91bmRlZC14bCBiZy1ncmFkaWVudC10by1iciBmcm9tLXRlYWwtODAwIHRvLXRlYWwtOTUwIHRleHQtd2hpdGUgZmxleCBpdGVtcy1jZW50ZXIganVzdGlmeS1jZW50ZXIiPiR7SWNvbihpY29uLCJ3LTUgaC01Iil9PC9kaXY+CiAgICA8c3BhbiBjbGFzcz0idGV4dC14cyBmb250LWJvbGQgdGV4dC1zdG9uZS03MDAiPiR7ZXNjKGxhYmVsKX08L3NwYW4+CiAgPC9idXR0b24+YDsKfQoKZnVuY3Rpb24gc2NyZWVuU3RhZmZEYXNoYm9hcmQoKSB7CiAgY29uc3QgcyA9IHN0YXRlLmFkbWluLnN0YXRzIHx8IHt9OwogIGNvbnN0IG5jID0gc3RhdGUuYWRtaW4ubm90aWZDZW50ZXIgfHwge307CiAgcmV0dXJuIGA8ZGl2IGNsYXNzPSJtYXgtdy0zeGwgbXgtYXV0byBwLTUgcGItMTAiPgogICAgJHtDYXJkKGA8ZGl2IGNsYXNzPSJwLTUgYmctZ3JhZGllbnQtdG8tbCBmcm9tLXRlYWwtOTAwIHZpYS10ZWFsLTgwMCB0by10ZWFsLTkwMCB0ZXh0LXdoaXRlIj4KICAgICAgPGRpdiBjbGFzcz0iZmxleCBpdGVtcy1jZW50ZXIganVzdGlmeS1iZXR3ZWVuIG1iLTEiPgogICAgICAgIDxidXR0b24gZGF0YS1hY3Rpb249InN0YWZmTG9nb3V0IiBjbGFzcz0idGV4dC10ZWFsLTEwMCB0ZXh0LXhzIGZvbnQtc2VtaWJvbGQgZmxleCBpdGVtcy1jZW50ZXIgZ2FwLTEgb3BhY2l0eS04MCBob3ZlcjpvcGFjaXR5LTEwMCI+JHtJY29uKCJsb2ctb3V0Iiwidy0zLjUgaC0zLjUiKX0g2K7YsdmI2Kw8L2J1dHRvbj4KICAgICAgICA8YnV0dG9uIGRhdGEtYWN0aW9uPSJnb0NoYW5nZVBhc3N3b3JkIiBjbGFzcz0idGV4dC10ZWFsLTEwMCB0ZXh0LXhzIGZvbnQtc2VtaWJvbGQgZmxleCBpdGVtcy1jZW50ZXIgZ2FwLTEgb3BhY2l0eS04MCBob3ZlcjpvcGFjaXR5LTEwMCI+JHtJY29uKCJrZXktcm91bmQiLCJ3LTMuNSBoLTMuNSIpfSDYqti624zbjNixINix2YXYsjwvYnV0dG9uPgogICAgICA8L2Rpdj4KICAgICAgPGRpdiBjbGFzcz0iZmxleCBpdGVtcy1jZW50ZXIgZ2FwLTMgbXQtMyI+CiAgICAgICAgPGRpdiBjbGFzcz0idy0xMSBoLTExIHJvdW5kZWQteGwgYmctd2hpdGUvMTAgZmxleCBpdGVtcy1jZW50ZXIganVzdGlmeS1jZW50ZXIiPiR7SWNvbigic2hpZWxkLWNoZWNrIiwidy02IGgtNiIpfTwvZGl2PgogICAgICAgIDxkaXY+PHAgY2xhc3M9ImZvbnQtZXh0cmFib2xkIHRleHQtbGciPtm+2YbZhCDZhdiv24zYsduM2Kog2YXYsdqp2LI8L3A+PHAgY2xhc3M9InRleHQteHMgdGV4dC10ZWFsLTIwMCI+JHtlc2Moc3RhdGUuc3RhZmYudXNlcm5hbWUpfSDCtyAke3N0YXRlLnN0YWZmLnJvbGU9PT0iYWRtaW4iPyLZhdiv24zYsSI6Itqp2KfYsdmF2YbYryJ9PC9wPjwvZGl2PgogICAgICA8L2Rpdj4KICAgIDwvZGl2PmAsICJtYi01IG92ZXJmbG93LWhpZGRlbiIpfQoKICAgICR7RXJyb3JCb3goc3RhdGUuZXJyb3JNc2cpfSR7VG9hc3Qoc3RhdGUudG9hc3QpfQoKICAgIDxkaXYgY2xhc3M9ImdyaWQgZ3JpZC1jb2xzLTMgZ2FwLTMgbWItNiI+CiAgICAgICR7TmF2VGlsZSgidXNlcnMiLCAi2KfZh9iv2KfaqdmG2YbYr9qv2KfZhiIsICJnb0Rvbm9yTGlzdCIpfQogICAgICAke05hdlRpbGUoImNhbGVuZGFyLWRheXMiLCAi2YbZiNio2KrigIzZh9inIiwgImdvQXBwb2ludG1lbnRzIil9CiAgICAgICR7TmF2VGlsZSgiYmVsbCIsICLYp9i52YTYp9mG4oCM2YfYpyIsICJnb05vdGlmQ2VudGVyIil9CiAgICAgICR7c3RhdGUuc3RhZmYucm9sZSA9PT0gImFkbWluIiA/IE5hdlRpbGUoImJhci1jaGFydC0zIiwgItix2YjYp9io2Lcg2LnZhdmI2YXbjCIsICJnb1ByRGFzaGJvYXJkIikgOiAiIn0KICAgICAgJHtzdGF0ZS5zdGFmZi5yb2xlID09PSAiYWRtaW4iID8gTmF2VGlsZSgiaGVhcnQtaGFuZHNoYWtlIiwgIkNSTSIsICJnb0NybURhc2hib2FyZCIpIDogIiJ9CiAgICAgICR7c3RhdGUuc3RhZmYucm9sZSA9PT0gImFkbWluIiA/IE5hdlRpbGUoInNldHRpbmdzIiwgItiq2YbYuNuM2YXYp9iqIiwgImdvU2V0dGluZ3MiKSA6ICIifQogICAgPC9kaXY+CgogICAgPGRpdiBjbGFzcz0iZ3JpZCBncmlkLWNvbHMtMiBzbTpncmlkLWNvbHMtNCBnYXAtMyBtYi02Ij4KICAgICAgJHtTdGF0Q2FyZCgidXNlci1wbHVzIiwgItir2KjYquKAjNmG2KfZhSDYrNiv24zYryDYp9mF2LHZiNiyIiwgcy5uZXdSZWdpc3RyYXRpb25zKX0KICAgICAgJHtTdGF0Q2FyZCgiZmxhc2stY29uaWNhbCIsICLZhdmG2KrYuNixINis2YjYp9ioINii2LLZhdin24zYtCIsIHMuYXdhaXRpbmdMYWIpfQogICAgICAke1N0YXRDYXJkKCJjaGVjay1jaXJjbGUtMiIsICLZvtmG2YTigIzZh9in24wg2YHYudin2YQiLCBzLmFjdGl2ZVBhbmVscyl9CiAgICAgICR7U3RhdENhcmQoImNhbGVuZGFyLWRheXMiLCAi2YbZiNio2KrigIzZh9in24wg2KfZhdix2YjYsiIsIHMudG9kYXlzQXBwb2ludG1lbnRzKX0KICAgICAgJHtTdGF0Q2FyZCgiZHJvcGxldCIsICLYp9mH2K/Yp9mH2KfbjCDYp9mG2KzYp9mF4oCM2LTYr9mHIiwgcy50b3RhbERvbmF0aW9ucyl9CiAgICAgICR7U3RhdENhcmQoInN0YXIiLCAi2K/Ysdi12K8g2LHYttin24zYqiIsIHMuc2F0aXNmYWN0aW9uUGVyY2VudCE9bnVsbCA/IGZhRGlnaXRzKHMuc2F0aXNmYWN0aW9uUGVyY2VudCkrIiUiIDogIi0iKX0KICAgIDwvZGl2PgoKICAgICR7Tm90aWZpY2F0aW9uQ2VudGVyUHJldmlldyhuYyl9CiAgPC9kaXY+YDsKfQoKZnVuY3Rpb24gTm90aWZpY2F0aW9uQ2VudGVyUHJldmlldyhuYykgewogIGNvbnN0IGFsZXJ0cyA9IG5jLmFsZXJ0cyB8fCBbXTsKICBjb25zdCBpdGVtcyA9IFsKICAgIC4uLihuYy5wZW5kaW5nTGFifHxbXSkuc2xpY2UoMCwzKS5tYXAoeCA9PiAoeyBpY29uOiImIzEyODMwOTsiLCB0ZXh0OmDZhtiq24zYrNmH4oCM24wg2KLYstmF2KfbjNi0ICR7eC5kb25vck5hbWV9INii2YXYp9iv2YfigIzbjCDYqtin24zbjNivYCwgcGhvbmU6eC5kb25vclBob25lIH0pKSwKICAgIC4uLihuYy5uZXdBcHBvaW50bWVudFJlcXVlc3RzfHxbXSkuc2xpY2UoMCwzKS5tYXAoeCA9PiAoeyBpY29uOiImIzEyODE5NzsiLCB0ZXh0OmDYr9ix2K7ZiNin2LPYqiDZhtmI2KjYqiDYrNiv24zYryDYp9iyICR7eC5kb25vck5hbWV9YCwgcGhvbmU6eC5kb25vclBob25lIH0pKSwKICAgIC4uLihuYy5kdWVSZW1pbmRlcnN8fFtdKS5zbGljZSgwLDMpLm1hcCh4ID0+ICh7IGljb246IiYjMTI4MjIyOyIsIHRleHQ6YNuM2KfYr9ii2YjYsTogJHt4LnR5cGV9IOKAlCAke3guZG9ub3JOYW1lfWAsIHBob25lOnguZG9ub3JQaG9uZSB9KSksCiAgICAuLi4obmMuZm9sbG93dXBzTmVlZGVkfHxbXSkuc2xpY2UoMCwzKS5tYXAoeCA9PiAoeyBpY29uOiImIzEwMDg0OyYjNjUwMzk7IiwgdGV4dDpg2b7bjNqv24zYsduMINm+2LMg2KfYsiDYp9mH2K/YpyDZhNin2LLZhSDYp9iz2Kog4oCUICR7eC5kb25vck5hbWV9YCwgcGhvbmU6eC5kb25vclBob25lIH0pKSwKICAgIC4uLihuYy5uZXdTdXJ2ZXlzfHxbXSkuc2xpY2UoMCwzKS5tYXAoeCA9PiAoeyBpY29uOiImIzExMDg4OyIsIHRleHQ6YNmG2LjYsdiz2YbYrNuMINis2K/bjNivINir2KjYqiDYtNivIOKAlCAke3guZG9ub3JOYW1lfWAsIHBob25lOnguZG9ub3JQaG9uZSB9KSksCiAgXTsKICBpZiAoYWxlcnRzLmxlbmd0aCA9PT0gMCAmJiBpdGVtcy5sZW5ndGggPT09IDApIHJldHVybiBDYXJkKGA8ZGl2IGNsYXNzPSJwLTYgdGV4dC1jZW50ZXIgdGV4dC1zbSB0ZXh0LXN0b25lLTQwMCI+2YHYudmE2KfZiyDaqdin2LHbjCDYr9ixINin2YbYqti42KfYsSDZhtuM2LPYqiDwn46JPC9kaXY+YCk7CiAgcmV0dXJuIGAKICAgICR7YWxlcnRzLmxlbmd0aCA+IDAgPyBDYXJkKGA8ZGl2IGNsYXNzPSJwLTQiPgogICAgICA8cCBjbGFzcz0idGV4dC14cyBmb250LWJvbGQgdGV4dC1yb3NlLTcwMCBtYi0zIj4mIzk4ODg7JiM2NTAzOTsg2YfYtNiv2KfYsdmH2KfbjCDZh9mI2LTZhdmG2K88L3A+CiAgICAgIDxkaXYgY2xhc3M9InNwYWNlLXktMiI+JHthbGVydHMuc2xpY2UoMCw4KS5tYXAoKGEpID0+IGAKICAgICAgICA8YnV0dG9uIGRhdGEtYWN0aW9uPSJvcGVuRG9ub3JCeVBob25lIiBkYXRhLXBob25lPSIke2VzYyhhLnBob25lKX0iIGNsYXNzPSJ3LWZ1bGwgdGV4dC1yaWdodCBwLTIuNSBiZy1yb3NlLTUwIHJvdW5kZWQtbGcgdGV4dC14cyB0ZXh0LXJvc2UtODAwIj4ke2VzYyhhLmRvbm9yTmFtZSl9IOKAlCAke2VzYyhhLmRldGFpbCl9PC9idXR0b24+CiAgICAgIGApLmpvaW4oIiIpfTwvZGl2PgogICAgPC9kaXY+YCwgIm1iLTQgYm9yZGVyLXJvc2UtMjAwIikgOiAiIn0KICAgICR7aXRlbXMubGVuZ3RoID4gMCA/IENhcmQoYDxkaXYgY2xhc3M9InAtNCI+CiAgICAgIDxwIGNsYXNzPSJ0ZXh0LXhzIGZvbnQtYm9sZCB0ZXh0LXRlYWwtODAwIG1iLTMiPiYjMTI4Mjc2OyDZhdix2qnYsiDYp9i52YTYp9mG4oCM2YfYpzwvcD4KICAgICAgPGRpdiBjbGFzcz0ic3BhY2UteS0yIj4ke2l0ZW1zLm1hcCgoaXQpID0+IGAKICAgICAgICA8YnV0dG9uIGRhdGEtYWN0aW9uPSJvcGVuRG9ub3JCeVBob25lIiBkYXRhLXBob25lPSIke2VzYyhpdC5waG9uZSl9IiBjbGFzcz0idy1mdWxsIHRleHQtcmlnaHQgcC0yLjUgYmctdGVhbC01MCByb3VuZGVkLWxnIHRleHQteHMgdGV4dC10ZWFsLTkwMCI+JHtpdC5pY29ufSAke2VzYyhpdC50ZXh0KX08L2J1dHRvbj4KICAgICAgYCkuam9pbigiIil9PC9kaXY+CiAgICAgIDxkaXYgY2xhc3M9Im10LTMiPiR7U21hbGxCdXR0b24oItmF2LTYp9mH2K/Zh+KAjNuMINmH2YXZhyIsICJnb05vdGlmQ2VudGVyIiwgeyB0b25lOiAic3RvbmUiIH0pfTwvZGl2PgogICAgPC9kaXY+YCkgOiAiIn0KICBgOwp9CgpmdW5jdGlvbiBzY3JlZW5Ob3RpZkNlbnRlcigpIHsKICBjb25zdCBuYyA9IHN0YXRlLmFkbWluLm5vdGlmQ2VudGVyIHx8IHt9OwogIHJldHVybiBgPGRpdiBjbGFzcz0ibWF4LXctMnhsIG14LWF1dG8gcC01IHBiLTEwIj4KICAgICR7VG9wQmFyKCLZhdix2qnYsiDYp9i52YTYp9mG4oCM2YfYpyIsICJnb1N0YWZmRGFzaGJvYXJkIil9CiAgICAke05vdGlmaWNhdGlvbkNlbnRlclByZXZpZXcoeyAuLi5uYywgcGVuZGluZ0xhYjogbmMucGVuZGluZ0xhYiwgbmV3QXBwb2ludG1lbnRSZXF1ZXN0czogbmMubmV3QXBwb2ludG1lbnRSZXF1ZXN0cywgZHVlUmVtaW5kZXJzOiBuYy5kdWVSZW1pbmRlcnMsIGZvbGxvd3Vwc05lZWRlZDogbmMuZm9sbG93dXBzTmVlZGVkLCBuZXdTdXJ2ZXlzOiBuYy5uZXdTdXJ2ZXlzIH0pfQogIDwvZGl2PmA7Cn0KCi8qID09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PQogICDZgdmH2LHYs9iqINin2YfYr9in2qnZhtmG2K/ar9in2YYgKyDYrNiz2KrYrNmICiAgID09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PSAqLwpmdW5jdGlvbiBzY3JlZW5Eb25vckxpc3QoKSB7CiAgY29uc3QgZG9ub3JzID0gc3RhdGUuYWRtaW4uZG9ub3JzIHx8IFtdOwogIHJldHVybiBgPGRpdiBjbGFzcz0ibWF4LXctMnhsIG14LWF1dG8gcC01IHBiLTEwIj4KICAgICR7VG9wQmFyKCLYp9mH2K/Yp9qp2YbZhtiv2q/Yp9mGIiwgImdvU3RhZmZEYXNoYm9hcmQiKX0KICAgICR7RXJyb3JCb3goc3RhdGUuZXJyb3JNc2cpfQogICAgPGRpdiBjbGFzcz0ibWItNCBmbGV4IGdhcC0yIj4KICAgICAgPGlucHV0IGlkPSJzZWFyY2hJbnB1dCIgdmFsdWU9IiR7ZXNjKHN0YXRlLmFkbWluLnF8fCIiKX0iIHBsYWNlaG9sZGVyPSLYrNiz2KrYrNmIINio2Kcg2YbYp9mFINuM2Kcg2LTZhdin2LHZhyDZhdmI2KjYp9uM2YQuLi4iIGNsYXNzPSJmbGV4LTEgYm9yZGVyIGJvcmRlci1zdG9uZS0yMDAgcm91bmRlZC14bCBweC00IHB5LTMiIC8+CiAgICAgICR7U21hbGxCdXR0b24oItis2LPYqtis2YgiLCAic2VhcmNoRG9ub3JzIiwgeyB0b25lOiAidGVhbCIgfSl9CiAgICA8L2Rpdj4KICAgICR7c3RhdGUuc3RhZmYucm9sZSA9PT0gImFkbWluIiA/IGA8ZGl2IGNsYXNzPSJtYi00Ij4ke1NtYWxsQnV0dG9uKCImIzEyODE5MDsg2K7YsdmI2KzbjCBFeGNlbCAoQ1NWKSIsICJleHBvcnRDc3YiLCB7IHRvbmU6ICJzdG9uZSIgfSl9PC9kaXY+YCA6ICIifQogICAgPGRpdiBjbGFzcz0ic3BhY2UteS0yIj4KICAgICAgJHtkb25vcnMubGVuZ3RoID09PSAwID8gYDxwIGNsYXNzPSJ0ZXh0LXNtIHRleHQtc3RvbmUtNDAwIHRleHQtY2VudGVyIHB5LTEwIj7Yp9mH2K/Yp9qp2YbZhtiv2YfigIzYp9uMINm+24zYr9inINmG2LTYrzwvcD5gIDogZG9ub3JzLm1hcCgoZCkgPT4gYAogICAgICAgIDxidXR0b24gZGF0YS1hY3Rpb249Im9wZW5Eb25vckJ5UGhvbmUiIGRhdGEtcGhvbmU9IiR7ZXNjKGQucGhvbmUpfSIgY2xhc3M9InctZnVsbCB0ZXh0LXJpZ2h0Ij4KICAgICAgICAgICR7Q2FyZChgPGRpdiBjbGFzcz0icC00IGZsZXggaXRlbXMtY2VudGVyIGp1c3RpZnktYmV0d2VlbiBob3Zlcjpib3JkZXItdGVhbC0zMDAiPgogICAgICAgICAgICA8ZGl2IGNsYXNzPSJmbGV4IGl0ZW1zLWNlbnRlciBnYXAtMyI+CiAgICAgICAgICAgICAgPGRpdiBjbGFzcz0idy0xMCBoLTEwIHJvdW5kZWQtZnVsbCBiZy10ZWFsLTkwMCB0ZXh0LXdoaXRlIGZsZXggaXRlbXMtY2VudGVyIGp1c3RpZnktY2VudGVyIGZvbnQtYm9sZCI+JHtlc2MoZC5maXJzdE5hbWUuY2hhckF0KDApKX08L2Rpdj4KICAgICAgICAgICAgICA8ZGl2PjxwIGNsYXNzPSJmb250LWJvbGQgdGV4dC10ZWFsLTk1MCI+JHtlc2MoZC5maXJzdE5hbWUpfSAke2VzYyhkLmxhc3ROYW1lKX08L3A+PHAgY2xhc3M9InRleHQteHMgdGV4dC1zdG9uZS00MDAiPiR7ZXNjKGQucGhvbmUpfSDCtyAke2ZhRGlnaXRzKGQuYXBwb2ludG1lbnRzLmZpbHRlcihhPT5hLmRvbmF0ZWQ9PT10cnVlKS5sZW5ndGgpfSDYp9mH2K/YpzwvcD48L2Rpdj4KICAgICAgICAgICAgPC9kaXY+CiAgICAgICAgICAgIDxkaXYgY2xhc3M9ImZsZXggaXRlbXMtY2VudGVyIGdhcC0yIj4KICAgICAgICAgICAgICAke2QuZmxhZ2dlZCA/IEJhZGdlKCLZvtuM2q/bjNix24wiLCJyb3NlIikgOiAiIn0KICAgICAgICAgICAgICAke0JhZGdlKFNUQVRVU19MQUJFTFNbZC5zdGF0dXNdfHxkLnN0YXR1cywgZC5zdGF0dXM9PT0iZG9uYXRlZCJ8fGQuc3RhdHVzPT09InJlYWR5Ij8iZW1lcmFsZCI6ZC5zdGF0dXM9PT0iYmxvY2tlZCI/InJvc2UiOiJzbGF0ZSIpfQogICAgICAgICAgICA8L2Rpdj4KICAgICAgICAgIDwvZGl2PmApfQogICAgICAgIDwvYnV0dG9uPgogICAgICBgKS5qb2luKCIiKX0KICAgIDwvZGl2PgogIDwvZGl2PmA7Cn0KCi8qID09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PQogICDYrNiy2KbbjNin2Kog2KfZh9iv2KfaqdmG2YbYr9mHIChDUk0pCiAgID09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PSAqLwpmdW5jdGlvbiBzY3JlZW5Eb25vckRldGFpbCgpIHsKICBjb25zdCBkID0gc3RhdGUuYWRtaW4uc2VsZWN0ZWREb25vcjsKICBpZiAoIWQpIHJldHVybiBgPGRpdiBjbGFzcz0icC0xMCB0ZXh0LWNlbnRlciB0ZXh0LXN0b25lLTQwMCI+2K/YsSDYrdin2YQg2KjYp9ix2q/YsNin2LHbjC4uLjwvZGl2PmA7CiAgcmV0dXJuIGA8ZGl2IGNsYXNzPSJtYXgtdy0yeGwgbXgtYXV0byBwLTUgcGItMTAiPgogICAgJHtUb3BCYXIoYCR7ZC5maXJzdE5hbWV9ICR7ZC5sYXN0TmFtZX1gLCAiZ29Eb25vckxpc3QiKX0KICAgICR7RXJyb3JCb3goc3RhdGUuZXJyb3JNc2cpfSR7VG9hc3Qoc3RhdGUudG9hc3QpfQoKICAgICR7Q2FyZChgPGRpdiBjbGFzcz0icC00Ij4KICAgICAgPGRpdiBjbGFzcz0iZmxleCBpdGVtcy1jZW50ZXIganVzdGlmeS1iZXR3ZWVuIG1iLTMiPgogICAgICAgIDxkaXY+PHAgY2xhc3M9InRleHQtc20gdGV4dC1zdG9uZS01MDAiPiR7ZXNjKGQucGhvbmUpfSDCtyAke2ZhRGlnaXRzKGQuYWdlKX0g2LPYp9mE2Yc8L3A+PHAgY2xhc3M9InRleHQteHMgdGV4dC1zdG9uZS00MDAiPti52LbZiNuM2Kog2KfYsiAke2ZtdERhdGUoZC5jcmVhdGVkQXQpfTwvcD48L2Rpdj4KICAgICAgICAke2QuZmxhZ2dlZCA/IEJhZGdlKCLZhtuM2KfYstmF2YbYryDZvtuM2q/bjNix24wiLCJyb3NlIikgOiAiIn0KICAgICAgPC9kaXY+CiAgICAgIDxsYWJlbCBjbGFzcz0idGV4dC14cyBmb250LXNlbWlib2xkIHRleHQtc3RvbmUtNTAwIj7ZiNi22LnbjNiqPC9sYWJlbD4KICAgICAgPHNlbGVjdCBkYXRhLWFjdGlvbj0iY2hhbmdlU3RhdHVzIiBjbGFzcz0idy1mdWxsIGJvcmRlciBib3JkZXItc3RvbmUtMjAwIHJvdW5kZWQteGwgcHgtNCBweS0zIG10LTEiPgogICAgICAgICR7T2JqZWN0LmVudHJpZXMoU1RBVFVTX0xBQkVMUykubWFwKChbayxsYWJlbF0pID0+IGA8b3B0aW9uIHZhbHVlPSIke2t9IiAke2Quc3RhdHVzPT09az8ic2VsZWN0ZWQiOiIifT4ke2xhYmVsfTwvb3B0aW9uPmApLmpvaW4oIiIpfQogICAgICA8L3NlbGVjdD4KICAgICAgPGRpdiBjbGFzcz0iZ3JpZCBncmlkLWNvbHMtMiBnYXAtMiBtdC0zIj4KICAgICAgICAke2Quc3RhdHVzID09PSAiYXdhaXRpbmdfbGFiIiA/IFNtYWxsQnV0dG9uKCLYqtin24zbjNivINmG2KrbjNis2YfigIzbjCDYotiy2YXYp9uM2LQiLCAiYXBwcm92ZUxhYiIsIHsgdG9uZTogImVtZXJhbGQiIH0pIDogIiJ9CiAgICAgICAgJHtkLnN0YXR1cyA9PT0gImJsb2NrZWQiCiAgICAgICAgICA/IFNtYWxsQnV0dG9uKCLYsdmB2Lkg2YXYs9iv2YjYr9uMIiwgInVuYmxvY2tEb25vciIsIHsgdG9uZTogImVtZXJhbGQiIH0pCiAgICAgICAgICA6IChzdGF0ZS5zdGFmZi5yb2xlID09PSAiYWRtaW4iID8gU21hbGxCdXR0b24oItmF2LPYr9mI2K/Ys9in2LLbjCIsICJibG9ja0Rvbm9yIiwgeyB0b25lOiAicm9zZSIgfSkgOiAiIil9CiAgICAgIDwvZGl2PgogICAgICAke3N0YXRlLnN0YWZmLnJvbGUgPT09ICJhZG1pbiIgPyBgPGRpdiBjbGFzcz0ibXQtMiI+JHtTbWFsbEJ1dHRvbigiJiMxMjg0NjU7JiM2NTAzOTsg2K3YsNmBINqp2KfZhdmEINin24zZhiDYp9mH2K/Yp9qp2YbZhtiv2YciLCAiZGVsZXRlRG9ub3IiLCB7IHRvbmU6ICJyb3NlIiwgY2xhc3NOYW1lOiAidy1mdWxsIiB9KX08L2Rpdj5gIDogIiJ9CiAgICA8L2Rpdj5gLCAibWItNCIpfQoKICAgICR7ZC5zdXJ2ZXkgPyBDYXJkKGA8ZGl2IGNsYXNzPSJwLTQiPgogICAgICA8ZGl2IGNsYXNzPSJmbGV4IGl0ZW1zLWNlbnRlciBqdXN0aWZ5LWJldHdlZW4gbWItMyI+CiAgICAgICAgPHAgY2xhc3M9InRleHQteHMgZm9udC1ib2xkIHRleHQtdGVhbC04MDAiPtmG2KrbjNis2YfigIzbjCDZhti42LHYs9mG2KzbjCDYp9mI2YTbjNmGINmF2LHYp9is2LnZhzwvcD4KICAgICAgICAke3N0YXRlLnN0YWZmLnJvbGUgPT09ICJhZG1pbiIgPyBgPGJ1dHRvbiBkYXRhLWFjdGlvbj0iZGVsZXRlU3VydmV5IiBjbGFzcz0idGV4dC14cyB0ZXh0LXJvc2UtNTAwIGZvbnQtYm9sZCI+2K3YsNmBINmG2LjYsdiz2YbYrNuMPC9idXR0b24+YCA6ICIifQogICAgICA8L2Rpdj4KICAgICAgPGRpdiBjbGFzcz0idGV4dC14cyB0ZXh0LXN0b25lLTYwMCBzcGFjZS15LTEiPgogICAgICAgICR7U1VSVkVZX0NBVEVHT1JJRVMubWFwKChba2V5LGxhYmVsXSkgPT4gYDxwPiR7bGFiZWx9OiA8Yj4ke2ZhRGlnaXRzKGQuc3VydmV5W2tleV0pfS/btTwvYj48L3A+YCkuam9pbigiIil9CiAgICAgICAgPHA+2KLYtNmG2KfbjNuMINio2Kcg2YXYsdqp2LI6IDxiPiR7ZXNjKGQuc3VydmV5LnJlZmVycmFsU291cmNlKX08L2I+PC9wPgogICAgICAgICR7ZC5zdXJ2ZXkuZnJlZVRleHQgPyBgPHAgY2xhc3M9Iml0YWxpYyBtdC0yIj7CqyR7ZXNjKGQuc3VydmV5LmZyZWVUZXh0KX3CuzwvcD5gIDogIiJ9CiAgICAgIDwvZGl2PgogICAgPC9kaXY+YCwgIm1iLTQiKSA6ICIifQoKICAgICR7QXBwb2ludG1lbnRzU2VjdGlvbihkKX0KICAgICR7Tm90ZXNTZWN0aW9uKGQpfQogICAgJHtSZW1pbmRlcnNTZWN0aW9uKGQpfQogICAgJHtUaW1lbGluZVNlY3Rpb24oZCl9CiAgPC9kaXY+YDsKfQoKZnVuY3Rpb24gQXBwb2ludG1lbnRzU2VjdGlvbihkKSB7CiAgY29uc3QgYWN0aXZlID0gZC5hcHBvaW50bWVudHMuZmlsdGVyKChhKSA9PiBhLnN0YXR1cyAhPT0gImNhbmNlbGxlZCIgJiYgYS5zdGF0dXMgIT09ICJjb21wbGV0ZWQiKTsKICByZXR1cm4gQ2FyZChgPGRpdiBjbGFzcz0icC00Ij4KICAgIDxwIGNsYXNzPSJ0ZXh0LXhzIGZvbnQtYm9sZCB0ZXh0LXRlYWwtODAwIG1iLTMiPtmG2YjYqNiq4oCM2YfYpzwvcD4KICAgICR7YWN0aXZlLmxlbmd0aCA9PT0gMCA/IGA8cCBjbGFzcz0idGV4dC14cyB0ZXh0LXN0b25lLTQwMCBtYi0yIj7ZhtmI2KjYqiDZgdi52KfZhNuMINmG24zYs9iqPC9wPmAgOiBhY3RpdmUubWFwKChhKSA9PiBgCiAgICAgIDxkaXYgY2xhc3M9ImJnLXN0b25lLTUwIHJvdW5kZWQteGwgcC0zIG1iLTIiPgogICAgICAgIDxwIGNsYXNzPSJ0ZXh0LXNtIGZvbnQtc2VtaWJvbGQgdGV4dC10ZWFsLTk1MCI+JHtmbXREYXRlVGltZShhLmNvbmZpcm1lZERhdGV8fGEucmVxdWVzdGVkRGF0ZSl9PC9wPgogICAgICAgIDxwIGNsYXNzPSJ0ZXh0LXhzIHRleHQtc3RvbmUtNDAwIG1iLTIiPiR7YS5zdGF0dXM9PT0icmVxdWVzdGVkIj8i2K/YsSDYp9mG2KrYuNin2LEg2KrYp9uM24zYryI6YS5zdGF0dXM9PT0iY29uZmlybWVkIj8i2KrYp9uM24zYr9i02K/ZhyI6YS5zdGF0dXM9PT0icmVzY2hlZHVsZWRfYnlfYWRtaW4iPyLYstmF2KfZhiDYrNiv24zYryDZvtuM2LTZhtmH2KfYryDYtNiv2YciOmEuc3RhdHVzfTwvcD4KICAgICAgICA8ZGl2IGNsYXNzPSJmbGV4IGZsZXgtd3JhcCBnYXAtMiI+CiAgICAgICAgICAke2Euc3RhdHVzPT09InJlcXVlc3RlZCIgPyBTbWFsbEJ1dHRvbigi2KrYp9uM24zYryIsICJjb25maXJtQXBwb2ludG1lbnQiLCB7IGRhdGE6e2lkOmEuaWR9LCB0b25lOiJlbWVyYWxkIiB9KSA6ICIifQogICAgICAgICAgJHtTbWFsbEJ1dHRvbigi2b7bjNi02YbZh9in2K8g2LLZhdin2YYg2K/bjNqv2LEiLCAicHJvcG9zZVJlc2NoZWR1bGUiLCB7IGRhdGE6e2lkOmEuaWR9LCB0b25lOiJzdG9uZSIgfSl9CiAgICAgICAgICAke1NtYWxsQnV0dG9uKCLZhNi62YgiLCAiY2FuY2VsQXBwdEFkbWluIiwgeyBkYXRhOntpZDphLmlkfSwgdG9uZToicm9zZSIgfSl9CiAgICAgICAgICAke1NtYWxsQnV0dG9uKCLYq9io2Kog2YbYqtuM2KzZh+KAjNuMINmF2LHYp9is2LnZhyIsICJvcGVuT3V0Y29tZUZvcm0iLCB7IGRhdGE6e2lkOmEuaWR9LCB0b25lOiJ0ZWFsIiB9KX0KICAgICAgICA8L2Rpdj4KICAgICAgPC9kaXY+CiAgICBgKS5qb2luKCIiKX0KICAgIDxkaXYgY2xhc3M9Im10LTMgcHQtMyBib3JkZXItdCBib3JkZXItc3RvbmUtMTAwIj4KICAgICAgPHAgY2xhc3M9InRleHQteHMgdGV4dC1zdG9uZS01MDAgbWItMiI+2KvYqNiqINmG2YjYqNiqINis2K/bjNivINio2LHYp9uMINin24zZhiDZgdix2K88L3A+CiAgICAgIDxkaXYgY2xhc3M9ImdyaWQgZ3JpZC1jb2xzLTIgZ2FwLTIgbWItMiI+CiAgICAgICAgPGlucHV0IGlkPSJhcHB0RGF0ZSIgdHlwZT0iZGF0ZSIgY2xhc3M9ImJvcmRlciBib3JkZXItc3RvbmUtMjAwIHJvdW5kZWQtbGcgcHgtMyBweS0yIHRleHQtc20iIC8+CiAgICAgICAgPGlucHV0IGlkPSJhcHB0VGltZSIgdHlwZT0idGltZSIgY2xhc3M9ImJvcmRlciBib3JkZXItc3RvbmUtMjAwIHJvdW5kZWQtbGcgcHgtMyBweS0yIHRleHQtc20iIC8+CiAgICAgIDwvZGl2PgogICAgICAke1NtYWxsQnV0dG9uKCLYq9io2Kog2Ygg2KrYp9uM24zYryDZhtmI2KjYqiIsICJjcmVhdGVBcHB0Rm9yRG9ub3IiLCB7IHRvbmU6ICJ0ZWFsIiB9KX0KICAgIDwvZGl2PgogIDwvZGl2PmAsICJtYi00Iik7Cn0KCmZ1bmN0aW9uIE5vdGVzU2VjdGlvbihkKSB7CiAgcmV0dXJuIENhcmQoYDxkaXYgY2xhc3M9InAtNCI+CiAgICA8cCBjbGFzcz0idGV4dC14cyBmb250LWJvbGQgdGV4dC10ZWFsLTgwMCBtYi0zIj4mIzEyODIyMTsg24zYp9iv2K/Yp9i02KrigIzZh9in24wg2K/Yp9iu2YTbjCAo2YHZgti3INio2LHYp9uMINqp2KfYsdqp2YbYp9mGKTwvcD4KICAgIDx0ZXh0YXJlYSBpZD0ibm90ZUlucHV0IiByb3dzPSIyIiBwbGFjZWhvbGRlcj0i2YXYq9mE2KfZizog2KjYp9ixINin2YjZhCDZhdix2KfYrNi52Ycg2qnYsdiv2Ycg2Ygg2qnZhduMINmF2LbYt9ix2Kgg2KjZiNivLi4uIiBjbGFzcz0idy1mdWxsIGJvcmRlciBib3JkZXItc3RvbmUtMjAwIHJvdW5kZWQtbGcgcHgtMyBweS0yIHRleHQtc20gbWItMiI+PC90ZXh0YXJlYT4KICAgICR7U21hbGxCdXR0b24oItin2YHYstmI2K/ZhiDbjNin2K/Yr9in2LTYqiIsICJhZGROb3RlIiwgeyB0b25lOiAidGVhbCIgfSl9CiAgICA8ZGl2IGNsYXNzPSJtdC0zIHNwYWNlLXktMiI+CiAgICAgICR7KGQubm90ZXN8fFtdKS5zbGljZSgpLnJldmVyc2UoKS5tYXAoKG4pID0+IGAKICAgICAgICA8ZGl2IGNsYXNzPSJiZy1zdG9uZS01MCByb3VuZGVkLWxnIHAtMi41IHRleHQteHMiPgogICAgICAgICAgPHAgY2xhc3M9InRleHQtc3RvbmUtNzAwIj4ke2VzYyhuLmJvZHkpfTwvcD4KICAgICAgICAgIDxkaXYgY2xhc3M9ImZsZXggaXRlbXMtY2VudGVyIGp1c3RpZnktYmV0d2VlbiBtdC0xIHRleHQtc3RvbmUtNDAwIj4KICAgICAgICAgICAgPHNwYW4+JHtlc2Mobi5hdXRob3JVc2VybmFtZSl9IMK3ICR7Zm10RGF0ZVNob3J0KG4uY3JlYXRlZEF0KX08L3NwYW4+CiAgICAgICAgICAgICR7c3RhdGUuc3RhZmYucm9sZSA9PT0gImFkbWluIiA/IGA8YnV0dG9uIGRhdGEtYWN0aW9uPSJkZWxldGVOb3RlIiBkYXRhLWlkPSIke24uaWR9IiBjbGFzcz0idGV4dC1yb3NlLTUwMCI+2K3YsNmBPC9idXR0b24+YCA6ICIifQogICAgICAgICAgPC9kaXY+CiAgICAgICAgPC9kaXY+CiAgICAgIGApLmpvaW4oIiIpfQogICAgPC9kaXY+CiAgPC9kaXY+YCwgIm1iLTQiKTsKfQoKZnVuY3Rpb24gUmVtaW5kZXJzU2VjdGlvbihkKSB7CiAgcmV0dXJuIENhcmQoYDxkaXYgY2xhc3M9InAtNCI+CiAgICA8cCBjbGFzcz0idGV4dC14cyBmb250LWJvbGQgdGV4dC10ZWFsLTgwMCBtYi0zIj4mIzkyMDA7INuM2KfYr9ii2YjYsdmH2KfbjCDZvtuM2q/bjNix24w8L3A+CiAgICA8ZGl2IGNsYXNzPSJncmlkIGdyaWQtY29scy0yIGdhcC0yIG1iLTIiPgogICAgICA8c2VsZWN0IGlkPSJyZW1pbmRlclR5cGUiIGNsYXNzPSJib3JkZXIgYm9yZGVyLXN0b25lLTIwMCByb3VuZGVkLWxnIHB4LTMgcHktMiB0ZXh0LXNtIj4KICAgICAgICAke1JFTUlOREVSX1RZUEVTLm1hcCgodCkgPT4gYDxvcHRpb24gdmFsdWU9IiR7ZXNjKHQpfSI+JHtlc2ModCl9PC9vcHRpb24+YCkuam9pbigiIil9CiAgICAgIDwvc2VsZWN0PgogICAgICA8aW5wdXQgaWQ9InJlbWluZGVyRGF0ZSIgdHlwZT0iZGF0ZXRpbWUtbG9jYWwiIGNsYXNzPSJib3JkZXIgYm9yZGVyLXN0b25lLTIwMCByb3VuZGVkLWxnIHB4LTMgcHktMiB0ZXh0LXNtIiAvPgogICAgPC9kaXY+CiAgICA8dGV4dGFyZWEgaWQ9InJlbWluZGVyTm90ZSIgcm93cz0iMSIgcGxhY2Vob2xkZXI9Itiq2YjYttuM2K0gKNin2K7YqtuM2KfYsduMKSIgY2xhc3M9InctZnVsbCBib3JkZXIgYm9yZGVyLXN0b25lLTIwMCByb3VuZGVkLWxnIHB4LTMgcHktMiB0ZXh0LXNtIG1iLTIiPjwvdGV4dGFyZWE+CiAgICAke1NtYWxsQnV0dG9uKCLYp9mB2LLZiNiv2YYg24zYp9iv2KLZiNixIiwgImFkZFJlbWluZGVyIiwgeyB0b25lOiAidGVhbCIgfSl9CiAgICA8ZGl2IGNsYXNzPSJtdC0zIHNwYWNlLXktMiI+CiAgICAgICR7KGQucmVtaW5kZXJzfHxbXSkuc2xpY2UoKS5yZXZlcnNlKCkubWFwKChyKSA9PiBgCiAgICAgICAgPGRpdiBjbGFzcz0iZmxleCBpdGVtcy1jZW50ZXIganVzdGlmeS1iZXR3ZWVuIGJnLXN0b25lLTUwIHJvdW5kZWQtbGcgcC0yLjUgdGV4dC14cyAke3IuZG9uZT8ib3BhY2l0eS01MCI6IiJ9Ij4KICAgICAgICAgIDxzcGFuPiR7ZXNjKHIudHlwZSl9IOKAlCAke2ZtdERhdGVUaW1lKHIuZHVlRGF0ZSl9JHtyLm5vdGU/IiDigJQgIitlc2Moci5ub3RlKToiIn08L3NwYW4+CiAgICAgICAgICAkeyFyLmRvbmUgPyBgPGJ1dHRvbiBkYXRhLWFjdGlvbj0ibWFya1JlbWluZGVyRG9uZSIgZGF0YS1pZD0iJHtyLmlkfSIgY2xhc3M9InRleHQtZW1lcmFsZC02MDAgZm9udC1ib2xkIj7Yp9mG2KzYp9mFINi02K88L2J1dHRvbj5gIDogYDxzcGFuIGNsYXNzPSJ0ZXh0LWVtZXJhbGQtNjAwIj7inJM8L3NwYW4+YH0KICAgICAgICA8L2Rpdj4KICAgICAgYCkuam9pbigiIil9CiAgICA8L2Rpdj4KICA8L2Rpdj5gLCAibWItNCIpOwp9CgpmdW5jdGlvbiBUaW1lbGluZVNlY3Rpb24oZCkgewogIHJldHVybiBDYXJkKGA8ZGl2IGNsYXNzPSJwLTQiPgogICAgPHAgY2xhc3M9InRleHQteHMgZm9udC1ib2xkIHRleHQtdGVhbC04MDAgbWItMyI+JiMxMjgzMzc7INiq2KfYsduM2K7ahtmH4oCM24wg2qnYp9mF2YQg2KfYsdiq2KjYp9i32KfYqjwvcD4KICAgIDxkaXYgY2xhc3M9InNwYWNlLXktMiBib3JkZXItci0yIGJvcmRlci10ZWFsLTEwMCBwci0zIj4KICAgICAgJHsoZC50aW1lbGluZXx8W10pLm1hcCgoZSkgPT4gYAogICAgICAgIDxkaXYgY2xhc3M9InRleHQteHMiPjxwIGNsYXNzPSJ0ZXh0LXN0b25lLTcwMCI+JHtlc2MoZS5sYWJlbCl9PC9wPjxwIGNsYXNzPSJ0ZXh0LXN0b25lLTQwMCI+JHtmbXREYXRlVGltZShlLmRhdGUpfTwvcD48L2Rpdj4KICAgICAgYCkuam9pbigiIil9CiAgICA8L2Rpdj4KICA8L2Rpdj5gKTsKfQoKLyogPT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09CiAgINmF2K/bjNix24zYqiDZhtmI2KjYquKAjNmH2KcKICAgPT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09ICovCmZ1bmN0aW9uIHNjcmVlbkFwcG9pbnRtZW50cygpIHsKICBjb25zdCBsaXN0ID0gc3RhdGUuYWRtaW4uYXBwb2ludG1lbnRzIHx8IFtdOwogIGNvbnN0IGRhdGUgPSBzdGF0ZS5hZG1pbi5zbG90RGF0ZSB8fCB0b2RheUlTT0RhdGUoKTsKICBjb25zdCBzbG90cyA9IHN0YXRlLmFkbWluLnNsb3RzIHx8IFtdOwogIHJldHVybiBgPGRpdiBjbGFzcz0ibWF4LXctMnhsIG14LWF1dG8gcC01IHBiLTEwIj4KICAgICR7VG9wQmFyKCLZhdiv24zYsduM2Kog2YbZiNio2KrigIzZh9inIiwgImdvU3RhZmZEYXNoYm9hcmQiKX0KICAgICR7RXJyb3JCb3goc3RhdGUuZXJyb3JNc2cpfSR7VG9hc3Qoc3RhdGUudG9hc3QpfQogICAgJHtDYXJkKGA8ZGl2IGNsYXNzPSJwLTQgbWItNCI+CiAgICAgIDxwIGNsYXNzPSJ0ZXh0LXhzIGZvbnQtYm9sZCB0ZXh0LXRlYWwtODAwIG1iLTIiPti42LHZgduM2Kog2LHZiNiyPC9wPgogICAgICA8ZGl2IGNsYXNzPSJmbGV4IGdhcC0yIG1iLTMiPgogICAgICAgIDxpbnB1dCBpZD0ic2xvdERhdGVJbnB1dCIgdHlwZT0iZGF0ZSIgdmFsdWU9IiR7ZGF0ZX0iIGNsYXNzPSJmbGV4LTEgYm9yZGVyIGJvcmRlci1zdG9uZS0yMDAgcm91bmRlZC1sZyBweC0zIHB5LTIgdGV4dC1zbSIgLz4KICAgICAgICAke1NtYWxsQnV0dG9uKCLZhtmF2KfbjNi0IiwgImxvYWRBZG1pblNsb3RzIiwgeyB0b25lOiAidGVhbCIgfSl9CiAgICAgIDwvZGl2PgogICAgICA8ZGl2IGNsYXNzPSJncmlkIGdyaWQtY29scy00IGdhcC0yIj4KICAgICAgICAke3Nsb3RzLm1hcCgocykgPT4gYDxkaXYgY2xhc3M9InRleHQtY2VudGVyIHAtMiByb3VuZGVkLWxnIHRleHQteHMgJHtzLmF2YWlsYWJsZT8iYmctZW1lcmFsZC01MCB0ZXh0LWVtZXJhbGQtNzAwIjoiYmctcm9zZS01MCB0ZXh0LXJvc2UtNjAwIn0iPiR7cy50aW1lfTxici8+JHtmYURpZ2l0cyhzLnVzZWQpfS8ke2ZhRGlnaXRzKHMuY2FwYWNpdHkpfTwvZGl2PmApLmpvaW4oIiIpfQogICAgICA8L2Rpdj4KICAgIDwvZGl2PmApfQogICAgPHAgY2xhc3M9InRleHQteHMgZm9udC1ib2xkIHRleHQtc3RvbmUtNDAwIG1iLTIiPtmG2YjYqNiq4oCM2YfYp9uMINm+24zYtOKAjNix2Yg8L3A+CiAgICA8ZGl2IGNsYXNzPSJzcGFjZS15LTIiPgogICAgICAke2xpc3QubGVuZ3RoPT09MCA/IGA8cCBjbGFzcz0idGV4dC1zbSB0ZXh0LXN0b25lLTQwMCB0ZXh0LWNlbnRlciBweS0xMCI+2YbZiNio2KrbjCDYq9io2Kog2YbYtNiv2Yc8L3A+YCA6IGxpc3QubWFwKChhKSA9PiBgCiAgICAgICAgPGJ1dHRvbiBkYXRhLWFjdGlvbj0ib3BlbkRvbm9yQnlQaG9uZSIgZGF0YS1waG9uZT0iJHtlc2MoYS5kb25vclBob25lKX0iIGNsYXNzPSJ3LWZ1bGwgdGV4dC1yaWdodCI+CiAgICAgICAgICAke0NhcmQoYDxkaXYgY2xhc3M9InAtMy41IGZsZXggaXRlbXMtY2VudGVyIGp1c3RpZnktYmV0d2VlbiI+CiAgICAgICAgICAgIDxkaXY+PHAgY2xhc3M9InRleHQtc20gZm9udC1zZW1pYm9sZCB0ZXh0LXRlYWwtOTUwIj4ke2VzYyhhLmRvbm9yTmFtZSl9PC9wPjxwIGNsYXNzPSJ0ZXh0LXhzIHRleHQtc3RvbmUtNDAwIj4ke2ZtdERhdGVUaW1lKGEuY29uZmlybWVkRGF0ZXx8YS5yZXF1ZXN0ZWREYXRlKX08L3A+PC9kaXY+CiAgICAgICAgICAgICR7QmFkZ2UoYS5zdGF0dXM9PT0icmVxdWVzdGVkIj8i2K/YsSDYp9mG2KrYuNin2LEiOmEuc3RhdHVzPT09ImNvbmZpcm1lZCI/Itiq2KfbjNuM2K/YtNiv2YciOmEuc3RhdHVzLCBhLnN0YXR1cz09PSJjb25maXJtZWQiPyJlbWVyYWxkIjoiYW1iZXIiKX0KICAgICAgICAgIDwvZGl2PmApfQogICAgICAgIDwvYnV0dG9uPgogICAgICBgKS5qb2luKCIiKX0KICAgIDwvZGl2PgogIDwvZGl2PmA7Cn0KCi8qID09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PQogICDYqtmG2LjbjNmF2KfYqiDZhdix2qnYsgogICA9PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT0gKi8KZnVuY3Rpb24gc2NyZWVuU2V0dGluZ3MoKSB7CiAgY29uc3QgcyA9IHN0YXRlLmFkbWluLnNldHRpbmdzIHx8IHt9OwogIGNvbnN0IHQgPSBzLnNtc1RlbXBsYXRlcyB8fCB7fTsKICByZXR1cm4gYDxkaXYgY2xhc3M9Im1heC13LXNtIG14LWF1dG8gcC01IHBiLTEwIj4KICAgICR7VG9wQmFyKCLYqtmG2LjbjNmF2KfYqiDZhdix2qnYsiIsICJnb1N0YWZmRGFzaGJvYXJkIil9JHtUb2FzdChzdGF0ZS50b2FzdCl9CiAgICAke0NhcmQoYDxkaXYgY2xhc3M9InAtNSBzcGFjZS15LTQiPgogICAgICA8cCBjbGFzcz0idGV4dC14cyBmb250LWJvbGQgdGV4dC10ZWFsLTgwMCI+2KrZhti424zZhdin2Kog2LnZhdmI2YXbjDwvcD4KICAgICAgPGRpdj48bGFiZWwgY2xhc3M9InRleHQteHMgdGV4dC1zdG9uZS01MDAiPtmG2KfZhSDZhdix2qnYsjwvbGFiZWw+PGlucHV0IGlkPSJzZXRDZW50ZXJOYW1lIiB2YWx1ZT0iJHtlc2Mocy5jZW50ZXJOYW1lfHwiIil9IiBjbGFzcz0idy1mdWxsIGJvcmRlciBib3JkZXItc3RvbmUtMjAwIHJvdW5kZWQteGwgcHgtNCBweS0zIG10LTEiIC8+PC9kaXY+CiAgICAgIDxkaXY+PGxhYmVsIGNsYXNzPSJ0ZXh0LXhzIHRleHQtc3RvbmUtNTAwIj7Zgdin2LXZhNmH4oCM24wg2YXYrNin2LIg2KjbjNmGINiv2Ygg2KfZh9iv2KcgKNix2YjYsik8L2xhYmVsPjxpbnB1dCBpZD0ic2V0R2FwRGF5cyIgdHlwZT0ibnVtYmVyIiBtaW49IjEiIHZhbHVlPSIke01hdGgucm91bmQoKHMubWluR2FwSG91cnN8fDI0MCkvMjQpfSIgY2xhc3M9InctZnVsbCBib3JkZXIgYm9yZGVyLXN0b25lLTIwMCByb3VuZGVkLXhsIHB4LTQgcHktMyBtdC0xIiAvPjwvZGl2PgogICAgICA8ZGl2IGNsYXNzPSJncmlkIGdyaWQtY29scy0yIGdhcC0zIj4KICAgICAgICA8ZGl2PjxsYWJlbCBjbGFzcz0idGV4dC14cyB0ZXh0LXN0b25lLTUwMCI+2LHZiNiy2YfYp9uMINm+24zar9uM2LHbjCDZvtizINin2LIg2KfZh9iv2Kc8L2xhYmVsPjxpbnB1dCBpZD0ic2V0Rm9sbG93RGF5cyIgdHlwZT0ibnVtYmVyIiBtaW49IjEiIHZhbHVlPSIke3MuZm9sbG93VXBEYXlzfHwxfSIgY2xhc3M9InctZnVsbCBib3JkZXIgYm9yZGVyLXN0b25lLTIwMCByb3VuZGVkLXhsIHB4LTQgcHktMyBtdC0xIiAvPjwvZGl2PgogICAgICAgIDxkaXY+PGxhYmVsIGNsYXNzPSJ0ZXh0LXhzIHRleHQtc3RvbmUtNTAwIj7Yr9mB2LnYp9iqINm+24zar9uM2LHbjCDYr9ixINix2YjYsjwvbGFiZWw+PGlucHV0IGlkPSJzZXRGb2xsb3dGcmVxIiB0eXBlPSJudW1iZXIiIG1pbj0iMSIgdmFsdWU9IiR7cy5mb2xsb3dVcEZyZXF1ZW5jeVBlckRheXx8MX0iIGNsYXNzPSJ3LWZ1bGwgYm9yZGVyIGJvcmRlci1zdG9uZS0yMDAgcm91bmRlZC14bCBweC00IHB5LTMgbXQtMSIgLz48L2Rpdj4KICAgICAgPC9kaXY+CiAgICAgIDxkaXYgY2xhc3M9ImdyaWQgZ3JpZC1jb2xzLTIgZ2FwLTMiPgogICAgICAgIDxkaXY+PGxhYmVsIGNsYXNzPSJ0ZXh0LXhzIHRleHQtc3RvbmUtNTAwIj7Ys9in2LnYqiDYtNix2YjYuSDZvtiw24zYsdi0PC9sYWJlbD48aW5wdXQgaWQ9InNldFN0YXJ0SG91ciIgdHlwZT0idGltZSIgdmFsdWU9IiR7cy5yZWNlcHRpb25TdGFydEhvdXJ8fCIwOTowMCJ9IiBjbGFzcz0idy1mdWxsIGJvcmRlciBib3JkZXItc3RvbmUtMjAwIHJvdW5kZWQteGwgcHgtNCBweS0zIG10LTEiIC8+PC9kaXY+CiAgICAgICAgPGRpdj48bGFiZWwgY2xhc3M9InRleHQteHMgdGV4dC1zdG9uZS01MDAiPtiz2KfYudiqINm+2KfbjNin2YYg2b7YsNuM2LHYtDwvbGFiZWw+PGlucHV0IGlkPSJzZXRFbmRIb3VyIiB0eXBlPSJ0aW1lIiB2YWx1ZT0iJHtzLnJlY2VwdGlvbkVuZEhvdXJ8fCIxNzowMCJ9IiBjbGFzcz0idy1mdWxsIGJvcmRlciBib3JkZXItc3RvbmUtMjAwIHJvdW5kZWQteGwgcHgtNCBweS0zIG10LTEiIC8+PC9kaXY+CiAgICAgIDwvZGl2PgogICAgICA8ZGl2PjxsYWJlbCBjbGFzcz0idGV4dC14cyB0ZXh0LXN0b25lLTUwMCBtYi0yIGJsb2NrIj7YsdmI2LLZh9in24wg2KrYudi324zZhNuMINmH2YHYqtqv24w8L2xhYmVsPgogICAgICAgIDxkaXYgY2xhc3M9ImdyaWQgZ3JpZC1jb2xzLTQgZ2FwLTIiPiR7V0VFS0RBWV9MQUJFTFMubWFwKChsYWJlbCxpZHgpID0+IGAKICAgICAgICAgIDxidXR0b24gZGF0YS1hY3Rpb249InRvZ2dsZUNsb3NlZERheSIgZGF0YS1kYXk9IiR7aWR4fSIgY2xhc3M9InB5LTIgcm91bmRlZC1sZyB0ZXh0LXhzIGZvbnQtc2VtaWJvbGQgYm9yZGVyICR7KHMuY2xvc2VkV2Vla2RheXN8fFtdKS5pbmNsdWRlcyhpZHgpPyJiZy1yb3NlLTYwMCB0ZXh0LXdoaXRlIGJvcmRlci1yb3NlLTYwMCI6ImJnLXdoaXRlIGJvcmRlci1zdG9uZS0yMDAgdGV4dC1zdG9uZS02MDAifSI+JHtsYWJlbH08L2J1dHRvbj4KICAgICAgICBgKS5qb2luKCIiKX08L2Rpdj4KICAgICAgPC9kaXY+CiAgICAgIDxkaXY+PGxhYmVsIGNsYXNzPSJ0ZXh0LXhzIHRleHQtc3RvbmUtNTAwIj7Yqti52LfbjNmE2KfYqiDYsdiz2YXbjC/Yp9iu2KrYtdin2LXbjCAo2YfYsSDYqtin2LHbjNiuINiv2LEg24zaqSDYrti32Iwg2YHYsdmF2KogWVlZWS1NTS1ERCk8L2xhYmVsPgogICAgICAgIDx0ZXh0YXJlYSBpZD0ic2V0SG9saWRheXMiIHJvd3M9IjMiIGNsYXNzPSJ3LWZ1bGwgYm9yZGVyIGJvcmRlci1zdG9uZS0yMDAgcm91bmRlZC14bCBweC00IHB5LTMgbXQtMSI+JHsocy5ob2xpZGF5c3x8W10pLmpvaW4oIlxuIil9PC90ZXh0YXJlYT4KICAgICAgPC9kaXY+CgogICAgICA8cCBjbGFzcz0idGV4dC14cyBmb250LWJvbGQgdGV4dC10ZWFsLTgwMCBwdC0yIj7ZhtmI2KjYquKAjNiv2YfbjDwvcD4KICAgICAgPGRpdj48bGFiZWwgY2xhc3M9InRleHQteHMgdGV4dC1zdG9uZS01MDAgbWItMiBibG9jayI+2K3Yp9mE2Kog2YbZiNio2KrigIzYr9mH24w8L2xhYmVsPgogICAgICAgIDxkaXYgY2xhc3M9ImdyaWQgZ3JpZC1jb2xzLTIgZ2FwLTIiPgogICAgICAgICAgPGJ1dHRvbiBkYXRhLWFjdGlvbj0ic2V0QXBwb2ludG1lbnRNb2RlIiBkYXRhLW1vZGU9ImF1dG8iIGNsYXNzPSJweS0yLjUgcm91bmRlZC1sZyB0ZXh0LXNtIGJvcmRlciAke3MuYXBwb2ludG1lbnRNb2RlPT09ImF1dG8iPyJiZy10ZWFsLTgwMCB0ZXh0LXdoaXRlIGJvcmRlci10ZWFsLTgwMCI6ImJnLXdoaXRlIGJvcmRlci1zdG9uZS0yMDAifSI+2K7ZiNiv2qnYp9ixPC9idXR0b24+CiAgICAgICAgICA8YnV0dG9uIGRhdGEtYWN0aW9uPSJzZXRBcHBvaW50bWVudE1vZGUiIGRhdGEtbW9kZT0ibWFudWFsIiBjbGFzcz0icHktMi41IHJvdW5kZWQtbGcgdGV4dC1zbSBib3JkZXIgJHtzLmFwcG9pbnRtZW50TW9kZT09PSJtYW51YWwiPyJiZy10ZWFsLTgwMCB0ZXh0LXdoaXRlIGJvcmRlci10ZWFsLTgwMCI6ImJnLXdoaXRlIGJvcmRlci1zdG9uZS0yMDAifSI+2KrYo9uM24zYryDYr9iz2KrbjDwvYnV0dG9uPgogICAgICAgIDwvZGl2PgogICAgICA8L2Rpdj4KICAgICAgPGRpdj48bGFiZWwgY2xhc3M9InRleHQteHMgdGV4dC1zdG9uZS01MDAiPti42LHZgduM2Kog2YfYsSDYs9in2LnYqiAo2YbZgdixKTwvbGFiZWw+PGlucHV0IGlkPSJzZXRDYXBhY2l0eSIgdHlwZT0ibnVtYmVyIiBtaW49IjEiIHZhbHVlPSIke3MuaG91cmx5Q2FwYWNpdHl8fDR9IiBjbGFzcz0idy1mdWxsIGJvcmRlciBib3JkZXItc3RvbmUtMjAwIHJvdW5kZWQteGwgcHgtNCBweS0zIG10LTEiIC8+PC9kaXY+CiAgICAgIDxkaXY+PGxhYmVsIGNsYXNzPSJ0ZXh0LXhzIHRleHQtc3RvbmUtNTAwIj7Zh9i02K/Yp9ixINi52K/ZhSDZhdix2KfYrNi52Ycg2KjYudivINin2LIgKNix2YjYsik8L2xhYmVsPjxpbnB1dCBpZD0ic2V0Tm9TaG93IiB0eXBlPSJudW1iZXIiIG1pbj0iMSIgdmFsdWU9IiR7cy5ub1Nob3dBbGVydERheXN8fDE0fSIgY2xhc3M9InctZnVsbCBib3JkZXIgYm9yZGVyLXN0b25lLTIwMCByb3VuZGVkLXhsIHB4LTQgcHktMyBtdC0xIiAvPjwvZGl2PgoKICAgICAgJHtQcmltYXJ5QnV0dG9uKCLYsNiu24zYsdmH4oCM24wg2KrZhti424zZhdin2KoiLCAic2F2ZVNldHRpbmdzIil9CiAgICA8L2Rpdj5gLCAibWItNSIpfQoKICAgICR7Q2FyZChgPGRpdiBjbGFzcz0icC01IHNwYWNlLXktMyI+CiAgICAgIDxwIGNsYXNzPSJ0ZXh0LXhzIGZvbnQtYm9sZCB0ZXh0LXRlYWwtODAwIj7Zhdiq2YYg2b7bjNin2YXaqeKAjNmH2KcgKNmC2KfYqNmEINmI24zYsdin24zYtCk8L3A+CiAgICAgICR7WyJyZWdpc3RyYXRpb24iLCJwYW5lbEFjdGl2YXRlZCIsImFwcG9pbnRtZW50Q29uZmlybWVkIiwiYXBwb2ludG1lbnRSZW1pbmRlciIsInBvc3REb25hdGlvbkZvbGxvd3VwIiwicmVib29raW5nRW5hYmxlZCJdLm1hcCgoa2V5KSA9PiBgCiAgICAgICAgPGRpdj48bGFiZWwgY2xhc3M9InRleHQteHMgdGV4dC1zdG9uZS01MDAiPiR7c21zVGVtcGxhdGVMYWJlbChrZXkpfTwvbGFiZWw+CiAgICAgICAgICA8dGV4dGFyZWEgaWQ9InRwbF8ke2tleX0iIHJvd3M9IjIiIGNsYXNzPSJ3LWZ1bGwgYm9yZGVyIGJvcmRlci1zdG9uZS0yMDAgcm91bmRlZC14bCBweC00IHB5LTMgbXQtMSI+JHtlc2ModFtrZXldfHwiIil9PC90ZXh0YXJlYT4KICAgICAgICA8L2Rpdj4KICAgICAgYCkuam9pbigiIil9CiAgICAgIDxwIGNsYXNzPSJ0ZXh0LXhzIHRleHQtc3RvbmUtNDAwIj7ZhduM4oCM2KrZiNmG24zYryDYp9iyIHtuYW1lfSDZiCB7Y2VudGVyTmFtZX0g2Ygge2RhdGV9INiv2KfYrtmEINmF2KrZhiDYp9iz2KrZgdin2K/ZhyDaqdmG24zYry48L3A+CiAgICAgICR7UHJpbWFyeUJ1dHRvbigi2LDYrtuM2LHZh+KAjNuMINmF2KrZhiDZvtuM2KfZhdqp4oCM2YfYpyIsICJzYXZlU21zVGVtcGxhdGVzIil9CiAgICA8L2Rpdj5gLCAibWItNSIpfQoKICAgICR7c3RhdGUuc3RhZmYucm9sZSA9PT0gImFkbWluIiA/IEdob3N0QnV0dG9uKCImIzEyODEwMDsg2YXYr9uM2LHbjNiqINqp2KfYsdqp2YbYp9mGIiwgImdvU3RhZmZVc2VycyIpIDogIiJ9CiAgPC9kaXY+YDsKfQpmdW5jdGlvbiBzbXNUZW1wbGF0ZUxhYmVsKGtleSkgewogIHJldHVybiB7IHJlZ2lzdHJhdGlvbjoi2b7bjNin2YUg2KvYqNiq4oCM2YbYp9mFIiwgcGFuZWxBY3RpdmF0ZWQ6Itm+24zYp9mFINmB2LnYp9mEINi02K/ZhiDZvtmG2YQiLCBhcHBvaW50bWVudENvbmZpcm1lZDoi2b7bjNin2YUg2KrYo9uM24zYryDZhtmI2KjYqiIsCiAgICBhcHBvaW50bWVudFJlbWluZGVyOiLZvtuM2KfZhSDbjNin2K/YotmI2LHbjCDZhtmI2KjYqiIsIHBvc3REb25hdGlvbkZvbGxvd3VwOiLZvtuM2KfZhSDZvtuM2q/bjNix24wg2KjYudivINin2LIg2KfZh9iv2KciLCByZWJvb2tpbmdFbmFibGVkOiLZvtuM2KfZhSDZgdi52KfZhCDYtNiv2YYg2LHYstix2Ygg2YXYrNiv2K8iIH1ba2V5XSB8fCBrZXk7Cn0KCi8qID09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PQogICDZhdiv24zYsduM2Kog2qnYp9ix2qnZhtin2YYKICAgPT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09ICovCmZ1bmN0aW9uIHNjcmVlblN0YWZmVXNlcnMoKSB7CiAgY29uc3QgdXNlcnMgPSBzdGF0ZS5hZG1pbi5zdGFmZkxpc3QgfHwgW107CiAgcmV0dXJuIGA8ZGl2IGNsYXNzPSJtYXgtdy1zbSBteC1hdXRvIHAtNSI+CiAgICAke1RvcEJhcigi2YXYr9uM2LHbjNiqINqp2KfYsdqp2YbYp9mGIiwgImdvU2V0dGluZ3MiKX0ke0Vycm9yQm94KHN0YXRlLmVycm9yTXNnKX0ke1RvYXN0KHN0YXRlLnRvYXN0KX0KICAgICR7Q2FyZChgPGRpdiBjbGFzcz0icC01IHNwYWNlLXktMyBtYi01Ij4KICAgICAgPHAgY2xhc3M9InRleHQteHMgZm9udC1ib2xkIHRleHQtdGVhbC04MDAiPtin2YHYstmI2K/ZhiDaqdin2LHZhdmG2K8g2KzYr9uM2K88L3A+CiAgICAgIDxpbnB1dCBpZD0ibmV3U3RhZmZVc2VybmFtZSIgcGxhY2Vob2xkZXI9ItmG2KfZhSDaqdin2LHYqNix24wiIGNsYXNzPSJ3LWZ1bGwgYm9yZGVyIGJvcmRlci1zdG9uZS0yMDAgcm91bmRlZC14bCBweC00IHB5LTMiIC8+CiAgICAgIDxpbnB1dCBpZD0ibmV3U3RhZmZQYXNzd29yZCIgdHlwZT0icGFzc3dvcmQiIHBsYWNlaG9sZGVyPSLYsdmF2LIg2YXZiNmC2KogKNit2K/Yp9mC2YQg27Yg2qnYp9ix2Kfaqdiq2LEpIiBjbGFzcz0idy1mdWxsIGJvcmRlciBib3JkZXItc3RvbmUtMjAwIHJvdW5kZWQteGwgcHgtNCBweS0zIiAvPgogICAgICA8c2VsZWN0IGlkPSJuZXdTdGFmZlJvbGUiIGNsYXNzPSJ3LWZ1bGwgYm9yZGVyIGJvcmRlci1zdG9uZS0yMDAgcm91bmRlZC14bCBweC00IHB5LTMiPgogICAgICAgIDxvcHRpb24gdmFsdWU9InN0YWZmIj7aqdin2LHZhdmG2K8g2LnYp9iv24w8L29wdGlvbj48b3B0aW9uIHZhbHVlPSJhZG1pbiI+2YXYr9uM2LE8L29wdGlvbj4KICAgICAgPC9zZWxlY3Q+CiAgICAgICR7UHJpbWFyeUJ1dHRvbigi2KfZgdiy2YjYr9mGIiwgImFkZFN0YWZmVXNlciIpfQogICAgPC9kaXY+YCl9CiAgICA8ZGl2IGNsYXNzPSJzcGFjZS15LTIiPgogICAgICAke3VzZXJzLm1hcCgodSkgPT4gYCR7Q2FyZChgPGRpdiBjbGFzcz0icC0zLjUgZmxleCBpdGVtcy1jZW50ZXIganVzdGlmeS1iZXR3ZWVuIj4KICAgICAgICA8ZGl2PjxwIGNsYXNzPSJmb250LXNlbWlib2xkIHRleHQtc20gdGV4dC10ZWFsLTk1MCI+JHtlc2ModS51c2VybmFtZSl9PC9wPjxwIGNsYXNzPSJ0ZXh0LXhzIHRleHQtc3RvbmUtNDAwIj4ke3Uucm9sZT09PSJhZG1pbiI/ItmF2K/bjNixIjoi2qnYp9ix2YXZhtivIn0ke3UuYmxvY2tlZD8iIMK3INmF2LPYr9mI2K8iOiIifTwvcD48L2Rpdj4KICAgICAgICA8ZGl2IGNsYXNzPSJmbGV4IGdhcC0yIj4KICAgICAgICAgICR7dS5pZCAhPT0gc3RhdGUuc3RhZmYuaWQgPyBgPGJ1dHRvbiBkYXRhLWFjdGlvbj0idG9nZ2xlQmxvY2tTdGFmZiIgZGF0YS1pZD0iJHt1LmlkfSIgZGF0YS1ibG9ja2VkPSIkeyF1LmJsb2NrZWR9IiBjbGFzcz0idGV4dC14cyB0ZXh0LWFtYmVyLTYwMCBmb250LWJvbGQiPiR7dS5ibG9ja2VkPyLYsdmB2Lkg2YXYs9iv2YjYr9uMIjoi2YXYs9iv2YjYryDaqdmGIn08L2J1dHRvbj4KICAgICAgICAgIDxidXR0b24gZGF0YS1hY3Rpb249ImRlbGV0ZVN0YWZmVXNlciIgZGF0YS1pZD0iJHt1LmlkfSIgY2xhc3M9InRleHQteHMgdGV4dC1yb3NlLTYwMCBmb250LWJvbGQiPtit2LDZgTwvYnV0dG9uPmAgOiBgPHNwYW4gY2xhc3M9InRleHQteHMgdGV4dC1zdG9uZS0zMDAiPtit2LPYp9ioINi02YXYpzwvc3Bhbj5gfQogICAgICAgIDwvZGl2PgogICAgICA8L2Rpdj5gKX1gKS5qb2luKCIiKX0KICAgIDwvZGl2PgogIDwvZGl2PmA7Cn0KCi8qID09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PQogICDYr9in2LTYqNmI2LHYryDYsdmI2KfYqNi3INi52YXZiNmF24wKICAgPT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09ICovCmZ1bmN0aW9uIHNjcmVlblByRGFzaGJvYXJkKCkgewogIGNvbnN0IHByID0gc3RhdGUuYWRtaW4ucHIgfHwge307CiAgY29uc3QgYXZncyA9IHByLmF2ZXJhZ2VzIHx8IHt9OwogIHJldHVybiBgPGRpdiBjbGFzcz0ibWF4LXctMnhsIG14LWF1dG8gcC01IHBiLTEwIj4KICAgICR7VG9wQmFyKCLYr9in2LTYqNmI2LHYryDYsdmI2KfYqNi3INi52YXZiNmF24wiLCAiZ29TdGFmZkRhc2hib2FyZCIpfQogICAgJHtDYXJkKGA8ZGl2IGNsYXNzPSJwLTUiPgogICAgICA8cCBjbGFzcz0idGV4dC14cyBmb250LWJvbGQgdGV4dC10ZWFsLTgwMCBtYi00Ij7ZhduM2KfZhtqv24zZhiDYsdi22KfbjNiqINin2LIg2YfYsSDZiNin2K3YryAo2KfYsiDbtSk8L3A+CiAgICAgICR7U1VSVkVZX0NBVEVHT1JJRVMubWFwKChba2V5LGxhYmVsXSkgPT4gQmFyUm93KGxhYmVsLCBhdmdzW2tleV18fDAsIDUsICJhbWJlciIpKS5qb2luKCIiKX0KICAgIDwvZGl2PmAsICJtYi01Iil9CiAgICAke0NhcmQoYDxkaXYgY2xhc3M9InAtNSI+CiAgICAgIDxwIGNsYXNzPSJ0ZXh0LXhzIGZvbnQtYm9sZCB0ZXh0LXRlYWwtODAwIG1iLTQiPtmG2K3ZiNmH4oCM24wg2KLYtNmG2KfbjNuMINmF2LHYp9is2LnZh+KAjNqp2YbZhtiv2q/Yp9mGPC9wPgogICAgICAkeyhwci5yZWZlcnJhbEJyZWFrZG93bnx8W10pLm1hcCgocikgPT4gQmFyUm93KGAke3Iuc291cmNlfSAoJHtmYURpZ2l0cyhyLnBlcmNlbnQpfSUpYCwgci5jb3VudCwgTWF0aC5tYXgoLi4uKHByLnJlZmVycmFsQnJlYWtkb3dufHxbe2NvdW50OjF9XSkubWFwKHg9PnguY291bnQpKSwgInRlYWwiKSkuam9pbigiIil9CiAgICA8L2Rpdj5gLCAibWItNSIpfQogICAgJHtDYXJkKGA8ZGl2IGNsYXNzPSJwLTUiPgogICAgICA8cCBjbGFzcz0idGV4dC14cyBmb250LWJvbGQgdGV4dC10ZWFsLTgwMCBtYi00Ij7YsdmI2YbYryDYsdi22KfbjNiqINiv2LEg2LfZiNmEINiy2YXYp9mGPC9wPgogICAgICAkeyhwci50cmVuZHx8W10pLm1hcCgodCkgPT4gQmFyUm93KHQubW9udGgsIHQuYXZnLCA1LCAiZW1lcmFsZCIpKS5qb2luKCIiKSB8fCBgPHAgY2xhc3M9InRleHQteHMgdGV4dC1zdG9uZS00MDAiPtiv2KfYr9mH4oCM24wg2qnYp9mB24wg2YbbjNiz2Ko8L3A+YH0KICAgIDwvZGl2PmAsICJtYi01Iil9CiAgICAke0NhcmQoYDxkaXYgY2xhc3M9InAtNSI+CiAgICAgIDxwIGNsYXNzPSJ0ZXh0LXhzIGZvbnQtYm9sZCB0ZXh0LXRlYWwtODAwIG1iLTQiPtm+24zYtNmG2YfYp9iv2YfYpyDZiCDYp9mG2KrZgtin2K/Yp9iqPC9wPgogICAgICAkeyhwci5jb21wbGFpbnRzfHxbXSkubGVuZ3RoPT09MCA/IGA8cCBjbGFzcz0idGV4dC14cyB0ZXh0LXN0b25lLTQwMCI+2YXZiNix2K/bjCDYq9io2Kog2YbYtNiv2Yc8L3A+YCA6IHByLmNvbXBsYWludHMubWFwKChjKSA9PiBgCiAgICAgICAgPGRpdiBjbGFzcz0iYmctc3RvbmUtNTAgcm91bmRlZC1sZyBwLTMgbWItMiB0ZXh0LXhzIj48cCBjbGFzcz0idGV4dC1zdG9uZS03MDAiPiR7ZXNjKGMudGV4dCl9PC9wPjxwIGNsYXNzPSJ0ZXh0LXN0b25lLTQwMCBtdC0xIj4ke2ZtdERhdGVTaG9ydChjLmRhdGUpfTwvcD48L2Rpdj4KICAgICAgYCkuam9pbigiIil9CiAgICA8L2Rpdj5gKX0KICAgIDxkaXYgY2xhc3M9Im10LTQgbm8tcHJpbnQiPiR7R2hvc3RCdXR0b24oIiYjMTI4NDI0OyYjNjUwMzk7INmG2LPYrtmH4oCM24wg2YLYp9io2YQg2obYp9m+IChQREYpIiwgInByaW50UmVwb3J0Iil9PC9kaXY+CiAgPC9kaXY+YDsKfQoKLyogPT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09CiAgINiv2KfYtNio2YjYsdivIENSTQogICA9PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT0gKi8KZnVuY3Rpb24gc2NyZWVuQ3JtRGFzaGJvYXJkKCkgewogIGNvbnN0IGMgPSBzdGF0ZS5hZG1pbi5jcm0gfHwge307CiAgcmV0dXJuIGA8ZGl2IGNsYXNzPSJtYXgtdy0yeGwgbXgtYXV0byBwLTUgcGItMTAiPgogICAgJHtUb3BCYXIoItiv2KfYtNio2YjYsdivIENSTSIsICJnb1N0YWZmRGFzaGJvYXJkIil9CiAgICA8ZGl2IGNsYXNzPSJncmlkIGdyaWQtY29scy0yIHNtOmdyaWQtY29scy00IGdhcC0zIG1iLTUiPgogICAgICAke1N0YXRDYXJkKCJ1c2VycyIsICLYp9mH2K/Yp9qp2YbZhtiv2q/Yp9mGINmB2LnYp9mEIiwgYy5hY3RpdmVEb25vcnMpfQogICAgICAke1N0YXRDYXJkKCJ1c2VyLXgiLCAi2LrbjNix2YHYudin2YQiLCBjLmluYWN0aXZlRG9ub3JzKX0KICAgICAgJHtTdGF0Q2FyZCgiYWxlcnQtdHJpYW5nbGUiLCAi2YbbjNin2LLZhdmG2K8g2b7bjNqv24zYsduMIiwgYy5uZWVkc0ZvbGxvd3VwKX0KICAgICAgJHtTdGF0Q2FyZCgiY2xvY2siLCAi24zYp9iv2KLZiNix2YfYp9uMINmF2LnZiNmCIiwgYy5wZW5kaW5nUmVtaW5kZXJzKX0KICAgIDwvZGl2PgogICAgJHtDYXJkKGA8ZGl2IGNsYXNzPSJwLTUiPgogICAgICA8cCBjbGFzcz0idGV4dC14cyBmb250LWJvbGQgdGV4dC10ZWFsLTgwMCBtYi00Ij7Yr9mE2KfbjNmEINin2LXZhNuMINmE2LrZiCDZhtmI2KjYqjwvcD4KICAgICAgJHsoYy5jYW5jZWxSZWFzb25zfHxbXSkubGVuZ3RoPT09MCA/IGA8cCBjbGFzcz0idGV4dC14cyB0ZXh0LXN0b25lLTQwMCI+2YTYutmI24wg2KvYqNiqINmG2LTYr9mHPC9wPmAgOiBjLmNhbmNlbFJlYXNvbnMubWFwKChyKSA9PiBCYXJSb3coci5yZWFzb24sIHIuY291bnQsIE1hdGgubWF4KC4uLmMuY2FuY2VsUmVhc29ucy5tYXAoeD0+eC5jb3VudCkpLCAicm9zZSIpKS5qb2luKCIiKX0KICAgIDwvZGl2PmAsICJtYi01Iil9CiAgICAke0NhcmQoYDxkaXYgY2xhc3M9InAtNSI+CiAgICAgIDxwIGNsYXNzPSJ0ZXh0LXhzIGZvbnQtYm9sZCB0ZXh0LXRlYWwtODAwIG1iLTQiPtmF2YfZheKAjNiq2LHbjNmGINmF2LPbjNix2YfYp9uMINis2LDYqDwvcD4KICAgICAgJHsoYy5yZWZlcnJhbEJyZWFrZG93bnx8W10pLm1hcCgocikgPT4gQmFyUm93KHIuc291cmNlLCByLmNvdW50LCBNYXRoLm1heCguLi4oYy5yZWZlcnJhbEJyZWFrZG93bnx8W3tjb3VudDoxfV0pLm1hcCh4PT54LmNvdW50KSksICJ0ZWFsIikpLmpvaW4oIiIpfQogICAgPC9kaXY+YCwgIm1iLTUiKX0KICAgICR7c3RhdGUuc3RhZmYucm9sZSA9PT0gImFkbWluIiA/IEdob3N0QnV0dG9uKCImIzEyODIyMDsg2YTYp9qvINmB2LnYp9mE24zYqiDaqdin2LHaqdmG2KfZhiIsICJnb0FjdGl2aXR5TG9nIikgOiAiIn0KICA8L2Rpdj5gOwp9CgpmdW5jdGlvbiBzY3JlZW5BY3Rpdml0eUxvZygpIHsKICBjb25zdCBsb2cgPSBzdGF0ZS5hZG1pbi5hY3Rpdml0eUxvZyB8fCBbXTsKICByZXR1cm4gYDxkaXYgY2xhc3M9Im1heC13LTJ4bCBteC1hdXRvIHAtNSBwYi0xMCI+CiAgICAke1RvcEJhcigi2YTYp9qvINmB2LnYp9mE24zYqiDaqdin2LHaqdmG2KfZhiIsICJnb0NybURhc2hib2FyZCIpfQogICAgPGRpdiBjbGFzcz0ic3BhY2UteS0yIj4KICAgICAgJHtsb2cubWFwKChhKSA9PiBgJHtDYXJkKGA8ZGl2IGNsYXNzPSJwLTMgdGV4dC14cyI+PHAgY2xhc3M9InRleHQtc3RvbmUtNzAwIj4ke2VzYyhhLmFjdG9yVXNlcm5hbWUpfSDigJQgJHtlc2MoYS5kZXRhaWwpfTwvcD48cCBjbGFzcz0idGV4dC1zdG9uZS00MDAgbXQtMSI+JHtmbXREYXRlVGltZShhLmNyZWF0ZWRBdCl9PC9wPjwvZGl2PmApfWApLmpvaW4oIiIpfQogICAgPC9kaXY+CiAgPC9kaXY+YDsKfQoKLyogPT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09CiAgINmB2LHZhSDYq9io2Kog2YbYqtuM2KzZh+KAjNuMINmF2LHYp9is2LnZhwogICA9PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT0gKi8KZnVuY3Rpb24gc2NyZWVuT3V0Y29tZUZvcm0oKSB7CiAgY29uc3QgZiA9IHN0YXRlLmZvcm07CiAgcmV0dXJuIGA8ZGl2IGNsYXNzPSJtYXgtdy1zbSBteC1hdXRvIHAtNSI+CiAgICAke1RvcEJhcigi2KvYqNiqINmG2KrbjNis2YfigIzbjCDZhdix2KfYrNi52YciLCAiYmFja1RvRG9ub3JEZXRhaWwiKX0ke0Vycm9yQm94KHN0YXRlLmVycm9yTXNnKX0KICAgICR7Q2FyZChgPGRpdiBjbGFzcz0icC01IHNwYWNlLXktNCI+CiAgICAgIDxsYWJlbCBjbGFzcz0iZmxleCBpdGVtcy1jZW50ZXIgZ2FwLTIgdGV4dC1zbSI+PGlucHV0IHR5cGU9ImNoZWNrYm94IiBkYXRhLWFjdGlvbj0idG9nZ2xlT3V0Y29tZUF0dGVuZGVkIiAke2YuYXR0ZW5kZWQ/ImNoZWNrZWQiOiIifSAvPiDZhdix2KfYrNi52Ycg2qnYsdivPC9sYWJlbD4KICAgICAgPGRpdj4KICAgICAgICA8cCBjbGFzcz0idGV4dC1zbSBmb250LXNlbWlib2xkIHRleHQtdGVhbC05NTAgbWItMiI+2YbYqtuM2KzZhzwvcD4KICAgICAgICA8ZGl2IGNsYXNzPSJncmlkIGdyaWQtY29scy0yIGdhcC0yIj4KICAgICAgICAgIDxidXR0b24gZGF0YS1hY3Rpb249InNldEZvcm0iIGRhdGEta2V5PSJkb25hdGVkIiBkYXRhLXZhbHVlPSJ0cnVlIiBjbGFzcz0icHktMi41IHJvdW5kZWQtbGcgdGV4dC1zbSBib3JkZXIgJHtmLmRvbmF0ZWQ9PT10cnVlPyJiZy1lbWVyYWxkLTYwMCB0ZXh0LXdoaXRlIGJvcmRlci1lbWVyYWxkLTYwMCI6ImJnLXdoaXRlIGJvcmRlci1zdG9uZS0yMDAifSI+2KfZh9iv2Kcg2KfZhtis2KfZhSDYtNivPC9idXR0b24+CiAgICAgICAgICA8YnV0dG9uIGRhdGEtYWN0aW9uPSJzZXRGb3JtIiBkYXRhLWtleT0iZG9uYXRlZCIgZGF0YS12YWx1ZT0iZmFsc2UiIGNsYXNzPSJweS0yLjUgcm91bmRlZC1sZyB0ZXh0LXNtIGJvcmRlciAke2YuZG9uYXRlZD09PWZhbHNlPyJiZy1yb3NlLTYwMCB0ZXh0LXdoaXRlIGJvcmRlci1yb3NlLTYwMCI6ImJnLXdoaXRlIGJvcmRlci1zdG9uZS0yMDAifSI+2KfZh9iv2Kcg2KfZhtis2KfZhSDZhti02K88L2J1dHRvbj4KICAgICAgICA8L2Rpdj4KICAgICAgPC9kaXY+CiAgICAgICR7Zi5kb25hdGVkID09PSBmYWxzZSA/IGA8ZGl2PjxsYWJlbCBjbGFzcz0idGV4dC14cyB0ZXh0LXN0b25lLTUwMCI+2LnZhNiqINi52K/ZhSDYp9mH2K/YpzwvbGFiZWw+PGlucHV0IGlkPSJub3REb25hdGVkUmVhc29uSW5wdXQiIGNsYXNzPSJ3LWZ1bGwgYm9yZGVyIGJvcmRlci1zdG9uZS0yMDAgcm91bmRlZC14bCBweC00IHB5LTMgbXQtMSIgLz48L2Rpdj5gIDogIiJ9CiAgICAgICR7UHJpbWFyeUJ1dHRvbigi2KvYqNiqINmG2KrbjNis2YciLCAic3VibWl0T3V0Y29tZSIpfQogICAgPC9kaXY+YCl9CiAgPC9kaXY+YDsKfQoKLyogPT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09CiAgINiv24zYs9m+2obYsSDYsdmG2K/YsQogICA9PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT0gKi8KZnVuY3Rpb24gcmVuZGVyKCkgewogIGNvbnN0IGFwcCA9IGRvY3VtZW50LmdldEVsZW1lbnRCeUlkKCJhcHAiKTsKICBsZXQgaHRtbDsKICBzd2l0Y2ggKHN0YXRlLnNjcmVlbikgewogICAgY2FzZSAibGFuZGluZyI6IGh0bWwgPSBzY3JlZW5MYW5kaW5nKCk7IGJyZWFrOwogICAgY2FzZSAiZG9ub3JPdHBQaG9uZSI6IGh0bWwgPSBzY3JlZW5Eb25vck90cFBob25lKCk7IGJyZWFrOwogICAgY2FzZSAiZG9ub3JPdHBDb2RlIjogaHRtbCA9IHNjcmVlbkRvbm9yT3RwQ29kZSgpOyBicmVhazsKICAgIGNhc2UgImRvbm9yUmVnaXN0ZXIiOiBodG1sID0gc2NyZWVuRG9ub3JSZWdpc3RlcigpOyBicmVhazsKICAgIGNhc2UgImRvbm9yU3VydmV5IjogaHRtbCA9IHNjcmVlbkRvbm9yU3VydmV5KCk7IGJyZWFrOwogICAgY2FzZSAiZG9ub3JUZXN0UGVuZGluZyI6IGh0bWwgPSBzY3JlZW5Eb25vclRlc3RQZW5kaW5nKCk7IGJyZWFrOwogICAgY2FzZSAiZG9ub3JIb21lIjogaHRtbCA9IHNjcmVlbkRvbm9ySG9tZSgpOyBicmVhazsKICAgIGNhc2UgImRvbm9yQm9vayI6IGh0bWwgPSBzY3JlZW5Eb25vckJvb2soKTsgYnJlYWs7CiAgICBjYXNlICJkb25vckZvbGxvd1VwIjogaHRtbCA9IHNjcmVlbkRvbm9yRm9sbG93VXAoKTsgYnJlYWs7CiAgICBjYXNlICJzdGFmZkxvZ2luIjogaHRtbCA9IHNjcmVlblN0YWZmTG9naW4oKTsgYnJlYWs7CiAgICBjYXNlICJjaGFuZ2VQYXNzd29yZCI6IGh0bWwgPSBzY3JlZW5DaGFuZ2VQYXNzd29yZCgpOyBicmVhazsKICAgIGNhc2UgInN0YWZmRGFzaGJvYXJkIjogaHRtbCA9IHNjcmVlblN0YWZmRGFzaGJvYXJkKCk7IGJyZWFrOwogICAgY2FzZSAibm90aWZDZW50ZXIiOiBodG1sID0gc2NyZWVuTm90aWZDZW50ZXIoKTsgYnJlYWs7CiAgICBjYXNlICJkb25vckxpc3QiOiBodG1sID0gc2NyZWVuRG9ub3JMaXN0KCk7IGJyZWFrOwogICAgY2FzZSAiZG9ub3JEZXRhaWwiOiBodG1sID0gc2NyZWVuRG9ub3JEZXRhaWwoKTsgYnJlYWs7CiAgICBjYXNlICJhcHBvaW50bWVudHMiOiBodG1sID0gc2NyZWVuQXBwb2ludG1lbnRzKCk7IGJyZWFrOwogICAgY2FzZSAic2V0dGluZ3MiOiBodG1sID0gc2NyZWVuU2V0dGluZ3MoKTsgYnJlYWs7CiAgICBjYXNlICJzdGFmZlVzZXJzIjogaHRtbCA9IHNjcmVlblN0YWZmVXNlcnMoKTsgYnJlYWs7CiAgICBjYXNlICJwckRhc2hib2FyZCI6IGh0bWwgPSBzY3JlZW5QckRhc2hib2FyZCgpOyBicmVhazsKICAgIGNhc2UgImNybURhc2hib2FyZCI6IGh0bWwgPSBzY3JlZW5Dcm1EYXNoYm9hcmQoKTsgYnJlYWs7CiAgICBjYXNlICJhY3Rpdml0eUxvZyI6IGh0bWwgPSBzY3JlZW5BY3Rpdml0eUxvZygpOyBicmVhazsKICAgIGNhc2UgIm91dGNvbWVGb3JtIjogaHRtbCA9IHNjcmVlbk91dGNvbWVGb3JtKCk7IGJyZWFrOwogICAgZGVmYXVsdDogaHRtbCA9IHNjcmVlbkxhbmRpbmcoKTsKICB9CiAgYXBwLmlubmVySFRNTCA9IGA8ZGl2IGNsYXNzPSJmYWRlLWluIj4ke2h0bWx9PC9kaXY+YDsKICBpZiAod2luZG93Lmx1Y2lkZSkgeyB0cnkgeyB3aW5kb3cubHVjaWRlLmNyZWF0ZUljb25zKCk7IH0gY2F0Y2ggKGUpIHt9IH0KfQoKLyogPT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09CiAgINin2qnYtNmG4oCM2YfYp9uMINin2YfYr9in2qnZhtmG2K/ZhwogICA9PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT0gKi8KZnVuY3Rpb24gZ29Eb25vckF1dGgoKSB7IHNldFNjcmVlbigiZG9ub3JPdHBQaG9uZSIpOyB9Cgphc3luYyBmdW5jdGlvbiByZXF1ZXN0T3RwKCkgewogIGNvbnN0IHBob25lID0gZG9jdW1lbnQuZ2V0RWxlbWVudEJ5SWQoInBob25lSW5wdXQiKS52YWx1ZS5yZXBsYWNlKC9bXjAtOV0vZywgIiIpOwogIGlmIChwaG9uZS5sZW5ndGggPCAxMCkgeyBzdGF0ZS5lcnJvck1zZyA9ICLYtNmF2KfYsdmHINmF2YjYqNin24zZhCDZhdi52KrYqNixINmG24zYs9iqIjsgcmVuZGVyKCk7IHJldHVybjsgfQogIHRyeSB7CiAgICBjb25zdCByZXMgPSBhd2FpdCBhcGkoIlBPU1QiLCAiL2FwaS9kb25vci1hdXRoL3JlcXVlc3Qtb3RwIiwgeyBwaG9uZSB9KTsKICAgIHN0YXRlLmZvcm0gPSB7IHBob25lLCBkZW1vQ29kZTogcmVzLmRlbW9Db2RlIH07CiAgICBzZXRTY3JlZW4oImRvbm9yT3RwQ29kZSIsIGZhbHNlKTsKICB9IGNhdGNoIChlKSB7IHN0YXRlLmVycm9yTXNnID0gZS5tZXNzYWdlOyByZW5kZXIoKTsgfQp9Cgphc3luYyBmdW5jdGlvbiB2ZXJpZnlPdHAoKSB7CiAgY29uc3QgY29kZSA9IGRvY3VtZW50LmdldEVsZW1lbnRCeUlkKCJvdHBJbnB1dCIpLnZhbHVlLnRyaW0oKTsKICB0cnkgewogICAgY29uc3QgcmVzID0gYXdhaXQgYXBpKCJQT1NUIiwgIi9hcGkvZG9ub3ItYXV0aC92ZXJpZnktb3RwIiwgeyBwaG9uZTogc3RhdGUuZm9ybS5waG9uZSwgY29kZSB9KTsKICAgIGlmIChyZXMuZXhpc3RzKSB7CiAgICAgIGF3YWl0IGxvYWREb25vckhvbWUoc3RhdGUuZm9ybS5waG9uZSk7CiAgICB9IGVsc2UgewogICAgICBzdGF0ZS5mb3JtID0geyBwaG9uZTogc3RhdGUuZm9ybS5waG9uZSB9OwogICAgICBzZXRTY3JlZW4oImRvbm9yUmVnaXN0ZXIiLCBmYWxzZSk7CiAgICB9CiAgfSBjYXRjaCAoZSkgeyBzdGF0ZS5lcnJvck1zZyA9IGUubWVzc2FnZTsgcmVuZGVyKCk7IH0KfQoKYXN5bmMgZnVuY3Rpb24gc3VibWl0UmVnaXN0ZXIoKSB7CiAgY29uc3QgZmlyc3ROYW1lID0gZG9jdW1lbnQuZ2V0RWxlbWVudEJ5SWQoImZpcnN0TmFtZUlucHV0IikudmFsdWUudHJpbSgpOwogIGNvbnN0IGxhc3ROYW1lID0gZG9jdW1lbnQuZ2V0RWxlbWVudEJ5SWQoImxhc3ROYW1lSW5wdXQiKS52YWx1ZS50cmltKCk7CiAgY29uc3QgYWdlID0gZG9jdW1lbnQuZ2V0RWxlbWVudEJ5SWQoImFnZUlucHV0IikudmFsdWU7CiAgdHJ5IHsKICAgIGF3YWl0IGFwaSgiUE9TVCIsICIvYXBpL2Rvbm9yLWF1dGgvcmVnaXN0ZXIiLCB7IHBob25lOiBzdGF0ZS5mb3JtLnBob25lLCBmaXJzdE5hbWUsIGxhc3ROYW1lLCBhZ2UgfSk7CiAgICBhd2FpdCBsb2FkRG9ub3JIb21lKHN0YXRlLmZvcm0ucGhvbmUpOwogIH0gY2F0Y2ggKGUpIHsgc3RhdGUuZXJyb3JNc2cgPSBlLm1lc3NhZ2U7IHJlbmRlcigpOyB9Cn0KCmFzeW5jIGZ1bmN0aW9uIGxvYWREb25vckhvbWUocGhvbmUpIHsKICB0cnkgewogICAgY29uc3QgZG9ub3IgPSBhd2FpdCBhcGkoIkdFVCIsIGAvYXBpL2Rvbm9ycy8ke3Bob25lfWApOwogICAgc3RhdGUuZG9ub3IgPSBkb25vcjsKICAgIHN0YXRlLmRvbm9yTm90aWZpY2F0aW9ucyA9IGF3YWl0IGFwaSgiR0VUIiwgYC9hcGkvZG9ub3JzLyR7cGhvbmV9L25vdGlmaWNhdGlvbnNgKTsKICAgIGlmICghZG9ub3Iuc3VydmV5KSBzZXRTY3JlZW4oImRvbm9yU3VydmV5IiwgdHJ1ZSk7CiAgICBlbHNlIGlmICghZG9ub3IubGFiQXBwcm92ZWRBdCkgc2V0U2NyZWVuKCJkb25vclRlc3RQZW5kaW5nIiwgdHJ1ZSk7CiAgICBlbHNlIHNldFNjcmVlbigiZG9ub3JIb21lIiwgdHJ1ZSk7CiAgfSBjYXRjaCAoZSkgeyBzdGF0ZS5lcnJvck1zZyA9IGUubWVzc2FnZTsgcmVuZGVyKCk7IH0KfQoKYXN5bmMgZnVuY3Rpb24gc3VibWl0U3VydmV5KCkgewogIGNvbnN0IGZyZWVUZXh0ID0gZG9jdW1lbnQuZ2V0RWxlbWVudEJ5SWQoImZyZWVUZXh0SW5wdXQiKS52YWx1ZS50cmltKCk7CiAgY29uc3QgcGF5bG9hZCA9IHsgLi4uc3RhdGUuZm9ybSwgZnJlZVRleHQgfTsKICBjb25zdCBwaG9uZSA9IHN0YXRlLmRvbm9yLnBob25lOwogIHRyeSB7CiAgICBhd2FpdCBhcGkoIlBPU1QiLCBgL2FwaS9kb25vcnMvJHtwaG9uZX0vc3VydmV5YCwgcGF5bG9hZCk7CiAgICBhd2FpdCBsb2FkRG9ub3JIb21lKHBob25lKTsKICB9IGNhdGNoIChlKSB7IHN0YXRlLmVycm9yTXNnID0gZS5tZXNzYWdlOyByZW5kZXIoKTsgfQp9CgpmdW5jdGlvbiBkb25vckxvZ291dEFjdGlvbigpIHsgc3RhdGUuZG9ub3IgPSBudWxsOyBzdGF0ZS5kb25vck5vdGlmaWNhdGlvbnMgPSBbXTsgc2V0U2NyZWVuKCJsYW5kaW5nIik7IH0KCmZ1bmN0aW9uIGJhY2tUb0Rvbm9ySG9tZSgpIHsgc2V0U2NyZWVuKCJkb25vckhvbWUiKTsgfQoKZnVuY3Rpb24gZ29Cb29rQXBwb2ludG1lbnQoKSB7CiAgc3RhdGUuZm9ybSA9IHsgYm9va0RhdGU6IHRvZGF5SVNPRGF0ZSgpLCBhcHBvaW50bWVudE1vZGU6ICJhdXRvIiB9OwogIGFwaSgiR0VUIiwgIi9hcGkvYWRtaW4vc2V0dGluZ3MiKS5jYXRjaCgoKSA9PiB7fSk7CiAgbG9hZFB1YmxpY1NldHRpbmdzRm9yQm9va2luZygpOwp9CmFzeW5jIGZ1bmN0aW9uIGxvYWRQdWJsaWNTZXR0aW5nc0ZvckJvb2tpbmcoKSB7CiAgdHJ5IHsKICAgIGNvbnN0IGRvbm9yID0gYXdhaXQgYXBpKCJHRVQiLCBgL2FwaS9kb25vcnMvJHtzdGF0ZS5kb25vci5waG9uZX1gKTsKICAgIHN0YXRlLmRvbm9yID0gZG9ub3I7CiAgfSBjYXRjaCAoZSkge30KICBzZXRTY3JlZW4oImRvbm9yQm9vayIsIGZhbHNlKTsKfQoKYXN5bmMgZnVuY3Rpb24gbG9hZFNsb3RzKCkgewogIGNvbnN0IGRhdGUgPSBkb2N1bWVudC5nZXRFbGVtZW50QnlJZCgiYm9va0RhdGVJbnB1dCIpLnZhbHVlOwogIHN0YXRlLmZvcm0uYm9va0RhdGUgPSBkYXRlOwogIHRyeSB7CiAgICBjb25zdCBzbG90cyA9IGF3YWl0IGFwaSgiR0VUIiwgYC9hcGkvZG9ub3JzLyR7c3RhdGUuZG9ub3IucGhvbmV9L3Nsb3RzP2RhdGU9JHtkYXRlfWApOwogICAgc3RhdGUuZm9ybS5zbG90cyA9IHNsb3RzOwogICAgcmVuZGVyKCk7CiAgfSBjYXRjaCAoZSkgeyBzdGF0ZS5lcnJvck1zZyA9IGUubWVzc2FnZTsgcmVuZGVyKCk7IH0KfQpmdW5jdGlvbiBwaWNrU2xvdCh0aW1lKSB7IHN0YXRlLmZvcm0ucGlja2VkVGltZSA9IHRpbWU7IHJlbmRlcigpOyB9Cgphc3luYyBmdW5jdGlvbiBzdWJtaXRCb29raW5nKCkgewogIGNvbnN0IGRhdGUgPSBkb2N1bWVudC5nZXRFbGVtZW50QnlJZCgiYm9va0RhdGVJbnB1dCIpLnZhbHVlOwogIGNvbnN0IGlzQXV0byA9IHN0YXRlLmZvcm0uYXBwb2ludG1lbnRNb2RlID09PSAiYXV0byI7CiAgY29uc3QgdGltZSA9IGlzQXV0byA/IHN0YXRlLmZvcm0ucGlja2VkVGltZSA6IChkb2N1bWVudC5nZXRFbGVtZW50QnlJZCgiYm9va1RpbWVJbnB1dCIpID8gZG9jdW1lbnQuZ2V0RWxlbWVudEJ5SWQoImJvb2tUaW1lSW5wdXQiKS52YWx1ZSA6ICIiKTsKICBjb25zdCBub3RlID0gZG9jdW1lbnQuZ2V0RWxlbWVudEJ5SWQoImJvb2tOb3RlSW5wdXQiKSA/IGRvY3VtZW50LmdldEVsZW1lbnRCeUlkKCJib29rTm90ZUlucHV0IikudmFsdWUgOiAiIjsKICB0cnkgewogICAgY29uc3QgZG9ub3IgPSBhd2FpdCBhcGkoIlBPU1QiLCBgL2FwaS9kb25vcnMvJHtzdGF0ZS5kb25vci5waG9uZX0vYXBwb2ludG1lbnRzYCwgeyBkYXRlLCB0aW1lLCBub3RlIH0pOwogICAgc3RhdGUuZG9ub3IgPSBkb25vcjsKICAgIHNob3dUb2FzdCgi2YbZiNio2Kog2KvYqNiqINi02K8iKTsKICAgIHNldFNjcmVlbigiZG9ub3JIb21lIik7CiAgfSBjYXRjaCAoZSkgeyBzdGF0ZS5lcnJvck1zZyA9IGUubWVzc2FnZTsgcmVuZGVyKCk7IH0KfQoKYXN5bmMgZnVuY3Rpb24gY2FuY2VsQXBwb2ludG1lbnQoaWQpIHsKICB0cnkgewogICAgc3RhdGUuZG9ub3IgPSBhd2FpdCBhcGkoIlBPU1QiLCBgL2FwaS9kb25vcnMvJHtzdGF0ZS5kb25vci5waG9uZX0vYXBwb2ludG1lbnRzLyR7aWR9L2NhbmNlbGApOwogICAgc2hvd1RvYXN0KCLZhtmI2KjYqiDZhNi62Ygg2LTYryIsICJyb3NlIik7CiAgICByZW5kZXIoKTsKICB9IGNhdGNoIChlKSB7IHN0YXRlLmVycm9yTXNnID0gZS5tZXNzYWdlOyByZW5kZXIoKTsgfQp9CmFzeW5jIGZ1bmN0aW9uIGFjY2VwdFJlc2NoZWR1bGUoaWQpIHsKICB0cnkgewogICAgc3RhdGUuZG9ub3IgPSBhd2FpdCBhcGkoIlBPU1QiLCBgL2FwaS9kb25vcnMvJHtzdGF0ZS5kb25vci5waG9uZX0vYXBwb2ludG1lbnRzLyR7aWR9L2FjY2VwdC1yZXNjaGVkdWxlYCk7CiAgICBzaG93VG9hc3QoItiy2YXYp9mGINis2K/bjNivINiq2KfbjNuM2K8g2LTYryIpOwogICAgcmVuZGVyKCk7CiAgfSBjYXRjaCAoZSkgeyBzdGF0ZS5lcnJvck1zZyA9IGUubWVzc2FnZTsgcmVuZGVyKCk7IH0KfQoKZnVuY3Rpb24gb3BlbkZvbGxvd1VwKGFwcHRJZCwgZGF5KSB7CiAgc3RhdGUuZm9ybSA9IHsgYXBwb2ludG1lbnRJZDogYXBwdElkLCBkYXlJbmRleDogZGF5IH07CiAgc2V0U2NyZWVuKCJkb25vckZvbGxvd1VwIiwgZmFsc2UpOwp9CmFzeW5jIGZ1bmN0aW9uIHN1Ym1pdEZvbGxvd1VwKCkgewogIGNvbnN0IG5vdGVzID0gZG9jdW1lbnQuZ2V0RWxlbWVudEJ5SWQoImZvbGxvd3VwTm90ZXMiKS52YWx1ZS50cmltKCk7CiAgY29uc3QgeyBhcHBvaW50bWVudElkLCBkYXlJbmRleCwgLi4uYW5zd2VycyB9ID0gc3RhdGUuZm9ybTsKICB0cnkgewogICAgc3RhdGUuZG9ub3IgPSBhd2FpdCBhcGkoIlBPU1QiLCBgL2FwaS9kb25vcnMvJHtzdGF0ZS5kb25vci5waG9uZX0vZm9sbG93dXBzLyR7YXBwb2ludG1lbnRJZH0vJHtkYXlJbmRleH1gLCB7IC4uLmFuc3dlcnMsIG5vdGVzIH0pOwogICAgc2hvd1RvYXN0KCLZhdmF2YbZiNmGINin2LIg2b7Yp9iz2K7igIzZh9in2KrZiNmGIPCfjL8iKTsKICAgIHNldFNjcmVlbigiZG9ub3JIb21lIik7CiAgfSBjYXRjaCAoZSkgeyBzdGF0ZS5lcnJvck1zZyA9IGUubWVzc2FnZTsgcmVuZGVyKCk7IH0KfQoKLyogPT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09CiAgINin2qnYtNmG4oCM2YfYp9uMINqp2KfYsdqp2YbYp9mGCiAgID09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PSAqLwphc3luYyBmdW5jdGlvbiBnb1N0YWZmTG9naW5BY3Rpb24oKSB7CiAgaWYgKHN0YXRlLnN0YWZmKSBhd2FpdCBnb1N0YWZmRGFzaGJvYXJkQWN0aW9uKCk7CiAgZWxzZSBzZXRTY3JlZW4oInN0YWZmTG9naW4iKTsKfQoKYXN5bmMgZnVuY3Rpb24gc3RhZmZMb2dpblN1Ym1pdCgpIHsKICBjb25zdCB1c2VybmFtZSA9IGRvY3VtZW50LmdldEVsZW1lbnRCeUlkKCJzdGFmZlVzZXJuYW1lIikudmFsdWUudHJpbSgpOwogIGNvbnN0IHBhc3N3b3JkID0gZG9jdW1lbnQuZ2V0RWxlbWVudEJ5SWQoInN0YWZmUGFzc3dvcmQiKS52YWx1ZTsKICB0cnkgewogICAgY29uc3Qgc3RhZmYgPSBhd2FpdCBhcGkoIlBPU1QiLCAiL2FwaS9zdGFmZi1hdXRoL2xvZ2luIiwgeyB1c2VybmFtZSwgcGFzc3dvcmQgfSk7CiAgICBzdGF0ZS5zdGFmZiA9IHN0YWZmOwogICAgaWYgKHN0YWZmLm11c3RDaGFuZ2VQYXNzd29yZCkgeyBzdGF0ZS5mb3JjZWRQd0NoYW5nZSA9IHRydWU7IHNldFNjcmVlbigiY2hhbmdlUGFzc3dvcmQiKTsgfQogICAgZWxzZSBhd2FpdCBnb1N0YWZmRGFzaGJvYXJkQWN0aW9uKCk7CiAgfSBjYXRjaCAoZSkgeyBzdGF0ZS5lcnJvck1zZyA9IGUubWVzc2FnZTsgcmVuZGVyKCk7IH0KfQoKYXN5bmMgZnVuY3Rpb24gc3VibWl0Q2hhbmdlUGFzc3dvcmQoKSB7CiAgY29uc3QgY3VycmVudFBhc3N3b3JkID0gZG9jdW1lbnQuZ2V0RWxlbWVudEJ5SWQoImN1clBhc3MiKS52YWx1ZTsKICBjb25zdCBuZXdQYXNzd29yZCA9IGRvY3VtZW50LmdldEVsZW1lbnRCeUlkKCJuZXdQYXNzIikudmFsdWU7CiAgdHJ5IHsKICAgIGF3YWl0IGFwaSgiUE9TVCIsICIvYXBpL3N0YWZmLWF1dGgvY2hhbmdlLXBhc3N3b3JkIiwgeyBjdXJyZW50UGFzc3dvcmQsIG5ld1Bhc3N3b3JkIH0pOwogICAgc2hvd1RvYXN0KCLYsdmF2LIg2LnYqNmI2LEg2KrYutuM24zYsSDaqdix2K8iKTsKICAgIHN0YXRlLmZvcmNlZFB3Q2hhbmdlID0gZmFsc2U7CiAgICBhd2FpdCBnb1N0YWZmRGFzaGJvYXJkQWN0aW9uKCk7CiAgfSBjYXRjaCAoZSkgeyBzdGF0ZS5lcnJvck1zZyA9IGUubWVzc2FnZTsgcmVuZGVyKCk7IH0KfQoKYXN5bmMgZnVuY3Rpb24gc3RhZmZMb2dvdXRBY3Rpb24oKSB7CiAgdHJ5IHsgYXdhaXQgYXBpKCJQT1NUIiwgIi9hcGkvc3RhZmYtYXV0aC9sb2dvdXQiKTsgfSBjYXRjaCAoZSkge30KICBzdGF0ZS5zdGFmZiA9IG51bGw7CiAgc2V0U2NyZWVuKCJsYW5kaW5nIik7Cn0KCmFzeW5jIGZ1bmN0aW9uIGdvU3RhZmZEYXNoYm9hcmRBY3Rpb24oKSB7CiAgdHJ5IHsKICAgIHN0YXRlLmFkbWluLnN0YXRzID0gYXdhaXQgYXBpKCJHRVQiLCAiL2FwaS9hZG1pbi9kYXNoYm9hcmQvc3RhdHMiKTsKICAgIHN0YXRlLmFkbWluLm5vdGlmQ2VudGVyID0gYXdhaXQgYXBpKCJHRVQiLCAiL2FwaS9hZG1pbi9ub3RpZmljYXRpb25zLWNlbnRlciIpOwogICAgc2V0U2NyZWVuKCJzdGFmZkRhc2hib2FyZCIpOwogIH0gY2F0Y2ggKGUpIHsgc3RhdGUuc3RhZmYgPSBudWxsOyBzdGF0ZS5lcnJvck1zZyA9IGUubWVzc2FnZTsgc2V0U2NyZWVuKCJzdGFmZkxvZ2luIik7IH0KfQoKYXN5bmMgZnVuY3Rpb24gZ29Ob3RpZkNlbnRlcigpIHsKICBzdGF0ZS5hZG1pbi5ub3RpZkNlbnRlciA9IGF3YWl0IGFwaSgiR0VUIiwgIi9hcGkvYWRtaW4vbm90aWZpY2F0aW9ucy1jZW50ZXIiKTsKICBzZXRTY3JlZW4oIm5vdGlmQ2VudGVyIik7Cn0KCmFzeW5jIGZ1bmN0aW9uIGdvRG9ub3JMaXN0KCkgewogIHN0YXRlLmFkbWluLmRvbm9ycyA9IGF3YWl0IGFwaSgiR0VUIiwgIi9hcGkvYWRtaW4vZG9ub3JzIik7CiAgc2V0U2NyZWVuKCJkb25vckxpc3QiKTsKfQphc3luYyBmdW5jdGlvbiBzZWFyY2hEb25vcnMoKSB7CiAgc3RhdGUuYWRtaW4ucSA9IGRvY3VtZW50LmdldEVsZW1lbnRCeUlkKCJzZWFyY2hJbnB1dCIpLnZhbHVlOwogIHN0YXRlLmFkbWluLmRvbm9ycyA9IGF3YWl0IGFwaSgiR0VUIiwgYC9hcGkvYWRtaW4vZG9ub3JzP3E9JHtlbmNvZGVVUklDb21wb25lbnQoc3RhdGUuYWRtaW4ucSl9YCk7CiAgcmVuZGVyKCk7Cn0KZnVuY3Rpb24gZXhwb3J0Q3N2KCkgeyB3aW5kb3cub3BlbigiL2FwaS9hZG1pbi9leHBvcnQvZG9ub3JzLmNzdiIsICJfYmxhbmsiKTsgfQoKYXN5bmMgZnVuY3Rpb24gb3BlbkRvbm9yQnlQaG9uZShwaG9uZSkgewogIHRyeSB7CiAgICBzdGF0ZS5hZG1pbi5zZWxlY3RlZERvbm9yID0gYXdhaXQgYXBpKCJHRVQiLCBgL2FwaS9hZG1pbi9kb25vcnMvJHtwaG9uZX1gKTsKICAgIHNldFNjcmVlbigiZG9ub3JEZXRhaWwiKTsKICB9IGNhdGNoIChlKSB7IHN0YXRlLmVycm9yTXNnID0gZS5tZXNzYWdlOyByZW5kZXIoKTsgfQp9CmFzeW5jIGZ1bmN0aW9uIHJlZnJlc2hTZWxlY3RlZERvbm9yKCkgewogIHN0YXRlLmFkbWluLnNlbGVjdGVkRG9ub3IgPSBhd2FpdCBhcGkoIkdFVCIsIGAvYXBpL2FkbWluL2Rvbm9ycy8ke3N0YXRlLmFkbWluLnNlbGVjdGVkRG9ub3IucGhvbmV9YCk7CiAgcmVuZGVyKCk7Cn0KZnVuY3Rpb24gYmFja1RvRG9ub3JEZXRhaWwoKSB7IHNldFNjcmVlbigiZG9ub3JEZXRhaWwiKTsgfQoKYXN5bmMgZnVuY3Rpb24gY2hhbmdlU3RhdHVzQWN0aW9uKHN0YXR1cykgewogIHRyeSB7IGF3YWl0IGFwaSgiUFVUIiwgYC9hcGkvYWRtaW4vZG9ub3JzLyR7c3RhdGUuYWRtaW4uc2VsZWN0ZWREb25vci5waG9uZX0vc3RhdHVzYCwgeyBzdGF0dXMgfSk7IGF3YWl0IHJlZnJlc2hTZWxlY3RlZERvbm9yKCk7IHNob3dUb2FzdCgi2YjYtti524zYqiDYqNix2YjYstix2LPYp9mG24wg2LTYryIpOyB9CiAgY2F0Y2ggKGUpIHsgc3RhdGUuZXJyb3JNc2cgPSBlLm1lc3NhZ2U7IHJlbmRlcigpOyB9Cn0KYXN5bmMgZnVuY3Rpb24gYXBwcm92ZUxhYigpIHsKICB0cnkgeyBhd2FpdCBhcGkoIlBPU1QiLCBgL2FwaS9hZG1pbi9kb25vcnMvJHtzdGF0ZS5hZG1pbi5zZWxlY3RlZERvbm9yLnBob25lfS9hcHByb3ZlLWxhYmApOyBhd2FpdCByZWZyZXNoU2VsZWN0ZWREb25vcigpOyBzaG93VG9hc3QoItmG2KrbjNis2Ycg2KrYp9uM24zYryDYtNivINmIINm+24zYp9mF2qkg2KfYsdiz2KfZhCDYtNivIik7IH0KICBjYXRjaCAoZSkgeyBzdGF0ZS5lcnJvck1zZyA9IGUubWVzc2FnZTsgcmVuZGVyKCk7IH0KfQphc3luYyBmdW5jdGlvbiBibG9ja0Rvbm9yKCkgewogIHRyeSB7IGF3YWl0IGFwaSgiUE9TVCIsIGAvYXBpL2FkbWluL2Rvbm9ycy8ke3N0YXRlLmFkbWluLnNlbGVjdGVkRG9ub3IucGhvbmV9L2Jsb2NrYCk7IGF3YWl0IHJlZnJlc2hTZWxlY3RlZERvbm9yKCk7IHNob3dUb2FzdCgi2YXYs9iv2YjYryDYtNivIiwgInJvc2UiKTsgfQogIGNhdGNoIChlKSB7IHN0YXRlLmVycm9yTXNnID0gZS5tZXNzYWdlOyByZW5kZXIoKTsgfQp9CmFzeW5jIGZ1bmN0aW9uIHVuYmxvY2tEb25vcigpIHsKICB0cnkgeyBhd2FpdCBhcGkoIlBPU1QiLCBgL2FwaS9hZG1pbi9kb25vcnMvJHtzdGF0ZS5hZG1pbi5zZWxlY3RlZERvbm9yLnBob25lfS91bmJsb2NrYCk7IGF3YWl0IHJlZnJlc2hTZWxlY3RlZERvbm9yKCk7IHNob3dUb2FzdCgi2LHZgdi5INmF2LPYr9mI2K/bjCDYtNivIik7IH0KICBjYXRjaCAoZSkgeyBzdGF0ZS5lcnJvck1zZyA9IGUubWVzc2FnZTsgcmVuZGVyKCk7IH0KfQphc3luYyBmdW5jdGlvbiBkZWxldGVEb25vcigpIHsKICBpZiAoIWNvbmZpcm0oYNii24zYpyDZhdi32YXYptmG24zYryDZhduM4oCM2K7ZiNin24zYryDCqyR7c3RhdGUuYWRtaW4uc2VsZWN0ZWREb25vci5maXJzdE5hbWV9ICR7c3RhdGUuYWRtaW4uc2VsZWN0ZWREb25vci5sYXN0TmFtZX3CuyDYsdmIINqp2KfZhdmEINit2LDZgSDaqdmG24zYr9ifINin24zZhiDaqdin2LEg2YLYp9io2YQg2KjYp9iy2q/YtNiqINmG24zYs9iqLmApKSByZXR1cm47CiAgdHJ5IHsKICAgIGNvbnN0IHBob25lID0gc3RhdGUuYWRtaW4uc2VsZWN0ZWREb25vci5waG9uZTsKICAgIGF3YWl0IGFwaSgiREVMRVRFIiwgYC9hcGkvYWRtaW4vZG9ub3JzLyR7cGhvbmV9YCk7CiAgICBzaG93VG9hc3QoItin2YfYr9in2qnZhtmG2K/ZhyDYrdiw2YEg2LTYryIsICJyb3NlIik7CiAgICBhd2FpdCBnb0Rvbm9yTGlzdCgpOwogIH0gY2F0Y2ggKGUpIHsgc3RhdGUuZXJyb3JNc2cgPSBlLm1lc3NhZ2U7IHJlbmRlcigpOyB9Cn0KYXN5bmMgZnVuY3Rpb24gZGVsZXRlU3VydmV5KCkgewogIGlmICghY29uZmlybSgi2YbYuNix2LPZhtis24wg2KfZiNmE24zZhiDZhdix2KfYrNi52YfigIzbjCDYp9uM2YYg2YHYsdivINit2LDZgSDYqNi02YfYnyIpKSByZXR1cm47CiAgdHJ5IHsgYXdhaXQgYXBpKCJERUxFVEUiLCBgL2FwaS9hZG1pbi9kb25vcnMvJHtzdGF0ZS5hZG1pbi5zZWxlY3RlZERvbm9yLnBob25lfS9zdXJ2ZXlgKTsgYXdhaXQgcmVmcmVzaFNlbGVjdGVkRG9ub3IoKTsgc2hvd1RvYXN0KCLZhti42LHYs9mG2KzbjCDYrdiw2YEg2LTYryIsICJyb3NlIik7IH0KICBjYXRjaCAoZSkgeyBzdGF0ZS5lcnJvck1zZyA9IGUubWVzc2FnZTsgcmVuZGVyKCk7IH0KfQoKYXN5bmMgZnVuY3Rpb24gYWRkTm90ZSgpIHsKICBjb25zdCBib2R5ID0gZG9jdW1lbnQuZ2V0RWxlbWVudEJ5SWQoIm5vdGVJbnB1dCIpLnZhbHVlLnRyaW0oKTsKICBpZiAoIWJvZHkpIHJldHVybjsKICB0cnkgeyBhd2FpdCBhcGkoIlBPU1QiLCBgL2FwaS9hZG1pbi9kb25vcnMvJHtzdGF0ZS5hZG1pbi5zZWxlY3RlZERvbm9yLnBob25lfS9ub3Rlc2AsIHsgYm9keSB9KTsgYXdhaXQgcmVmcmVzaFNlbGVjdGVkRG9ub3IoKTsgfQogIGNhdGNoIChlKSB7IHN0YXRlLmVycm9yTXNnID0gZS5tZXNzYWdlOyByZW5kZXIoKTsgfQp9CmFzeW5jIGZ1bmN0aW9uIGRlbGV0ZU5vdGUoaWQpIHsKICB0cnkgeyBhd2FpdCBhcGkoIkRFTEVURSIsIGAvYXBpL2FkbWluL2Rvbm9ycy8ke3N0YXRlLmFkbWluLnNlbGVjdGVkRG9ub3IucGhvbmV9L25vdGVzLyR7aWR9YCk7IGF3YWl0IHJlZnJlc2hTZWxlY3RlZERvbm9yKCk7IH0KICBjYXRjaCAoZSkgeyBzdGF0ZS5lcnJvck1zZyA9IGUubWVzc2FnZTsgcmVuZGVyKCk7IH0KfQoKYXN5bmMgZnVuY3Rpb24gYWRkUmVtaW5kZXIoKSB7CiAgY29uc3QgdHlwZSA9IGRvY3VtZW50LmdldEVsZW1lbnRCeUlkKCJyZW1pbmRlclR5cGUiKS52YWx1ZTsKICBjb25zdCBkdWVEYXRlID0gZG9jdW1lbnQuZ2V0RWxlbWVudEJ5SWQoInJlbWluZGVyRGF0ZSIpLnZhbHVlOwogIGNvbnN0IG5vdGUgPSBkb2N1bWVudC5nZXRFbGVtZW50QnlJZCgicmVtaW5kZXJOb3RlIikudmFsdWUudHJpbSgpOwogIGlmICghZHVlRGF0ZSkgeyBzdGF0ZS5lcnJvck1zZyA9ICLYqtin2LHbjNiuINuM2KfYr9ii2YjYsSDYsdmIINin2YbYqtiu2KfYqCDaqdmG24zYryI7IHJlbmRlcigpOyByZXR1cm47IH0KICB0cnkgeyBhd2FpdCBhcGkoIlBPU1QiLCBgL2FwaS9hZG1pbi9kb25vcnMvJHtzdGF0ZS5hZG1pbi5zZWxlY3RlZERvbm9yLnBob25lfS9yZW1pbmRlcnNgLCB7IHR5cGUsIGR1ZURhdGU6IG5ldyBEYXRlKGR1ZURhdGUpLnRvSVNPU3RyaW5nKCksIG5vdGUgfSk7IGF3YWl0IHJlZnJlc2hTZWxlY3RlZERvbm9yKCk7IHNob3dUb2FzdCgi24zYp9iv2KLZiNixINir2KjYqiDYtNivIik7IH0KICBjYXRjaCAoZSkgeyBzdGF0ZS5lcnJvck1zZyA9IGUubWVzc2FnZTsgcmVuZGVyKCk7IH0KfQphc3luYyBmdW5jdGlvbiBtYXJrUmVtaW5kZXJEb25lKGlkKSB7CiAgdHJ5IHsgYXdhaXQgYXBpKCJQT1NUIiwgYC9hcGkvYWRtaW4vZG9ub3JzLyR7c3RhdGUuYWRtaW4uc2VsZWN0ZWREb25vci5waG9uZX0vcmVtaW5kZXJzLyR7aWR9L2RvbmVgKTsgYXdhaXQgcmVmcmVzaFNlbGVjdGVkRG9ub3IoKTsgfQogIGNhdGNoIChlKSB7IHN0YXRlLmVycm9yTXNnID0gZS5tZXNzYWdlOyByZW5kZXIoKTsgfQp9Cgphc3luYyBmdW5jdGlvbiBjb25maXJtQXBwb2ludG1lbnQoaWQpIHsKICB0cnkgeyBhd2FpdCBhcGkoIlBPU1QiLCBgL2FwaS9hZG1pbi9kb25vcnMvJHtzdGF0ZS5hZG1pbi5zZWxlY3RlZERvbm9yLnBob25lfS9hcHBvaW50bWVudHMvJHtpZH0vY29uZmlybWAsIHt9KTsgYXdhaXQgcmVmcmVzaFNlbGVjdGVkRG9ub3IoKTsgc2hvd1RvYXN0KCLZhtmI2KjYqiDYqtin24zbjNivINmIINm+24zYp9mF2qkg2KfYsdiz2KfZhCDYtNivIik7IH0KICBjYXRjaCAoZSkgeyBzdGF0ZS5lcnJvck1zZyA9IGUubWVzc2FnZTsgcmVuZGVyKCk7IH0KfQphc3luYyBmdW5jdGlvbiBwcm9wb3NlUmVzY2hlZHVsZShpZCkgewogIGNvbnN0IGRhdGUgPSBwcm9tcHQoItiq2KfYsduM2K4g2Ygg2LPYp9i52Kog2b7bjNi02YbZh9in2K/bjCDYsdinINmI2KfYsdivINqp2YbbjNivICjZhdir2KfZhDogMjAyNi0wOC0wMVQxMDowMCkiKTsKICBpZiAoIWRhdGUpIHJldHVybjsKICB0cnkgeyBhd2FpdCBhcGkoIlBPU1QiLCBgL2FwaS9hZG1pbi9kb25vcnMvJHtzdGF0ZS5hZG1pbi5zZWxlY3RlZERvbm9yLnBob25lfS9hcHBvaW50bWVudHMvJHtpZH0vcHJvcG9zZWAsIHsgZGF0ZSB9KTsgYXdhaXQgcmVmcmVzaFNlbGVjdGVkRG9ub3IoKTsgc2hvd1RvYXN0KCLYstmF2KfZhiDZvtuM2LTZhtmH2KfYr9uMINir2KjYqiDYtNivIik7IH0KICBjYXRjaCAoZSkgeyBzdGF0ZS5lcnJvck1zZyA9IGUubWVzc2FnZTsgcmVuZGVyKCk7IH0KfQphc3luYyBmdW5jdGlvbiBjYW5jZWxBcHB0QWRtaW4oaWQpIHsKICB0cnkgeyBhd2FpdCBhcGkoIlBPU1QiLCBgL2FwaS9hZG1pbi9kb25vcnMvJHtzdGF0ZS5hZG1pbi5zZWxlY3RlZERvbm9yLnBob25lfS9hcHBvaW50bWVudHMvJHtpZH0vY2FuY2VsYCwge30pOyBhd2FpdCByZWZyZXNoU2VsZWN0ZWREb25vcigpOyBzaG93VG9hc3QoItmG2YjYqNiqINmE2LrZiCDYtNivIiwgInJvc2UiKTsgfQogIGNhdGNoIChlKSB7IHN0YXRlLmVycm9yTXNnID0gZS5tZXNzYWdlOyByZW5kZXIoKTsgfQp9CmZ1bmN0aW9uIG9wZW5PdXRjb21lRm9ybShpZCkgeyBzdGF0ZS5mb3JtID0geyBhcHB0SWQ6IGlkLCBhdHRlbmRlZDogdHJ1ZSwgZG9uYXRlZDogbnVsbCB9OyBzZXRTY3JlZW4oIm91dGNvbWVGb3JtIiwgZmFsc2UpOyB9CmZ1bmN0aW9uIHRvZ2dsZU91dGNvbWVBdHRlbmRlZCgpIHsgc3RhdGUuZm9ybS5hdHRlbmRlZCA9ICFzdGF0ZS5mb3JtLmF0dGVuZGVkOyByZW5kZXIoKTsgfQphc3luYyBmdW5jdGlvbiBzdWJtaXRPdXRjb21lKCkgewogIGNvbnN0IG5vdERvbmF0ZWRSZWFzb24gPSBkb2N1bWVudC5nZXRFbGVtZW50QnlJZCgibm90RG9uYXRlZFJlYXNvbklucHV0IikgPyBkb2N1bWVudC5nZXRFbGVtZW50QnlJZCgibm90RG9uYXRlZFJlYXNvbklucHV0IikudmFsdWUgOiAiIjsKICB0cnkgewogICAgYXdhaXQgYXBpKCJQT1NUIiwgYC9hcGkvYWRtaW4vZG9ub3JzLyR7c3RhdGUuYWRtaW4uc2VsZWN0ZWREb25vci5waG9uZX0vYXBwb2ludG1lbnRzLyR7c3RhdGUuZm9ybS5hcHB0SWR9L291dGNvbWVgLCB7IGF0dGVuZGVkOiBzdGF0ZS5mb3JtLmF0dGVuZGVkLCBkb25hdGVkOiBzdGF0ZS5mb3JtLmRvbmF0ZWQsIG5vdERvbmF0ZWRSZWFzb24gfSk7CiAgICBhd2FpdCByZWZyZXNoU2VsZWN0ZWREb25vcigpOwogICAgc2hvd1RvYXN0KCLZhtiq24zYrNmHINir2KjYqiDYtNivIik7CiAgICBzZXRTY3JlZW4oImRvbm9yRGV0YWlsIik7CiAgfSBjYXRjaCAoZSkgeyBzdGF0ZS5lcnJvck1zZyA9IGUubWVzc2FnZTsgcmVuZGVyKCk7IH0KfQphc3luYyBmdW5jdGlvbiBjcmVhdGVBcHB0Rm9yRG9ub3IoKSB7CiAgY29uc3QgZGF0ZSA9IGRvY3VtZW50LmdldEVsZW1lbnRCeUlkKCJhcHB0RGF0ZSIpLnZhbHVlOwogIGNvbnN0IHRpbWUgPSBkb2N1bWVudC5nZXRFbGVtZW50QnlJZCgiYXBwdFRpbWUiKS52YWx1ZSB8fCAiMDk6MDAiOwogIGlmICghZGF0ZSkgeyBzdGF0ZS5lcnJvck1zZyA9ICLYqtin2LHbjNiuINix2Ygg2KfZhtiq2K7Yp9ioINqp2YbbjNivIjsgcmVuZGVyKCk7IHJldHVybjsgfQogIHRyeSB7CiAgICBhd2FpdCBhcGkoIlBPU1QiLCBgL2FwaS9hZG1pbi9kb25vcnMvJHtzdGF0ZS5hZG1pbi5zZWxlY3RlZERvbm9yLnBob25lfS9hcHBvaW50bWVudHNgLCB7IGRhdGUsIHRpbWUgfSk7CiAgICBhd2FpdCByZWZyZXNoU2VsZWN0ZWREb25vcigpOwogICAgc2hvd1RvYXN0KCLZhtmI2KjYqiDYq9io2Kog2Ygg2KrYp9uM24zYryDYtNivIik7CiAgfSBjYXRjaCAoZSkgeyBzdGF0ZS5lcnJvck1zZyA9IGUubWVzc2FnZTsgcmVuZGVyKCk7IH0KfQoKYXN5bmMgZnVuY3Rpb24gZ29BcHBvaW50bWVudHMoKSB7CiAgc3RhdGUuYWRtaW4uYXBwb2ludG1lbnRzID0gYXdhaXQgYXBpKCJHRVQiLCAiL2FwaS9hZG1pbi9hcHBvaW50bWVudHMiKTsKICBzdGF0ZS5hZG1pbi5zbG90RGF0ZSA9IHRvZGF5SVNPRGF0ZSgpOwogIHNldFNjcmVlbigiYXBwb2ludG1lbnRzIik7Cn0KYXN5bmMgZnVuY3Rpb24gbG9hZEFkbWluU2xvdHMoKSB7CiAgY29uc3QgZGF0ZSA9IGRvY3VtZW50LmdldEVsZW1lbnRCeUlkKCJzbG90RGF0ZUlucHV0IikudmFsdWU7CiAgc3RhdGUuYWRtaW4uc2xvdERhdGUgPSBkYXRlOwogIHN0YXRlLmFkbWluLnNsb3RzID0gYXdhaXQgYXBpKCJHRVQiLCBgL2FwaS9hZG1pbi9hcHBvaW50bWVudHMvc2xvdHM/ZGF0ZT0ke2RhdGV9YCk7CiAgcmVuZGVyKCk7Cn0KCmFzeW5jIGZ1bmN0aW9uIGdvU2V0dGluZ3MoKSB7CiAgc3RhdGUuYWRtaW4uc2V0dGluZ3MgPSBhd2FpdCBhcGkoIkdFVCIsICIvYXBpL2FkbWluL3NldHRpbmdzIik7CiAgc2V0U2NyZWVuKCJzZXR0aW5ncyIpOwp9CmZ1bmN0aW9uIHRvZ2dsZUNsb3NlZERheShkYXkpIHsKICBjb25zdCBzID0gc3RhdGUuYWRtaW4uc2V0dGluZ3M7CiAgY29uc3QgaWR4ID0gcy5jbG9zZWRXZWVrZGF5cy5pbmRleE9mKGRheSk7CiAgaWYgKGlkeCA+PSAwKSBzLmNsb3NlZFdlZWtkYXlzLnNwbGljZShpZHgsIDEpOyBlbHNlIHMuY2xvc2VkV2Vla2RheXMucHVzaChkYXkpOwogIHJlbmRlcigpOwp9CmZ1bmN0aW9uIHNldEFwcG9pbnRtZW50TW9kZShtb2RlKSB7IHN0YXRlLmFkbWluLnNldHRpbmdzLmFwcG9pbnRtZW50TW9kZSA9IG1vZGU7IHJlbmRlcigpOyB9CmFzeW5jIGZ1bmN0aW9uIHNhdmVTZXR0aW5ncygpIHsKICBjb25zdCBwYXlsb2FkID0gewogICAgY2VudGVyTmFtZTogZG9jdW1lbnQuZ2V0RWxlbWVudEJ5SWQoInNldENlbnRlck5hbWUiKS52YWx1ZS50cmltKCksCiAgICBtaW5HYXBIb3VyczogTnVtYmVyKGRvY3VtZW50LmdldEVsZW1lbnRCeUlkKCJzZXRHYXBEYXlzIikudmFsdWUpICogMjQsCiAgICBmb2xsb3dVcERheXM6IE51bWJlcihkb2N1bWVudC5nZXRFbGVtZW50QnlJZCgic2V0Rm9sbG93RGF5cyIpLnZhbHVlKSwKICAgIGZvbGxvd1VwRnJlcXVlbmN5UGVyRGF5OiBOdW1iZXIoZG9jdW1lbnQuZ2V0RWxlbWVudEJ5SWQoInNldEZvbGxvd0ZyZXEiKS52YWx1ZSksCiAgICByZWNlcHRpb25TdGFydEhvdXI6IGRvY3VtZW50LmdldEVsZW1lbnRCeUlkKCJzZXRTdGFydEhvdXIiKS52YWx1ZSwKICAgIHJlY2VwdGlvbkVuZEhvdXI6IGRvY3VtZW50LmdldEVsZW1lbnRCeUlkKCJzZXRFbmRIb3VyIikudmFsdWUsCiAgICBjbG9zZWRXZWVrZGF5czogc3RhdGUuYWRtaW4uc2V0dGluZ3MuY2xvc2VkV2Vla2RheXMsCiAgICBob2xpZGF5czogZG9jdW1lbnQuZ2V0RWxlbWVudEJ5SWQoInNldEhvbGlkYXlzIikudmFsdWUuc3BsaXQoIlxuIikubWFwKChzKSA9PiBzLnRyaW0oKSkuZmlsdGVyKEJvb2xlYW4pLAogICAgYXBwb2ludG1lbnRNb2RlOiBzdGF0ZS5hZG1pbi5zZXR0aW5ncy5hcHBvaW50bWVudE1vZGUsCiAgICBob3VybHlDYXBhY2l0eTogTnVtYmVyKGRvY3VtZW50LmdldEVsZW1lbnRCeUlkKCJzZXRDYXBhY2l0eSIpLnZhbHVlKSwKICAgIG5vU2hvd0FsZXJ0RGF5czogTnVtYmVyKGRvY3VtZW50LmdldEVsZW1lbnRCeUlkKCJzZXROb1Nob3ciKS52YWx1ZSksCiAgfTsKICB0cnkgeyBzdGF0ZS5hZG1pbi5zZXR0aW5ncyA9IGF3YWl0IGFwaSgiUFVUIiwgIi9hcGkvYWRtaW4vc2V0dGluZ3MiLCBwYXlsb2FkKTsgc2hvd1RvYXN0KCLYqtmG2LjbjNmF2KfYqiDYsNiu24zYsdmHINi02K8iKTsgcmVuZGVyKCk7IH0KICBjYXRjaCAoZSkgeyBzdGF0ZS5lcnJvck1zZyA9IGUubWVzc2FnZTsgcmVuZGVyKCk7IH0KfQphc3luYyBmdW5jdGlvbiBzYXZlU21zVGVtcGxhdGVzKCkgewogIGNvbnN0IGtleXMgPSBbInJlZ2lzdHJhdGlvbiIsInBhbmVsQWN0aXZhdGVkIiwiYXBwb2ludG1lbnRDb25maXJtZWQiLCJhcHBvaW50bWVudFJlbWluZGVyIiwicG9zdERvbmF0aW9uRm9sbG93dXAiLCJyZWJvb2tpbmdFbmFibGVkIl07CiAgY29uc3QgcGF5bG9hZCA9IHt9OwogIGtleXMuZm9yRWFjaCgoaykgPT4geyBwYXlsb2FkW2tdID0gZG9jdW1lbnQuZ2V0RWxlbWVudEJ5SWQoInRwbF8iICsgaykudmFsdWU7IH0pOwogIHRyeSB7IGF3YWl0IGFwaSgiUFVUIiwgIi9hcGkvYWRtaW4vc2V0dGluZ3Mvc21zLXRlbXBsYXRlcyIsIHBheWxvYWQpOyBzaG93VG9hc3QoItmF2KrZhiDZvtuM2KfZhdqp4oCM2YfYpyDYsNiu24zYsdmHINi02K8iKTsgfQogIGNhdGNoIChlKSB7IHN0YXRlLmVycm9yTXNnID0gZS5tZXNzYWdlOyByZW5kZXIoKTsgfQp9Cgphc3luYyBmdW5jdGlvbiBnb1N0YWZmVXNlcnMoKSB7CiAgc3RhdGUuYWRtaW4uc3RhZmZMaXN0ID0gYXdhaXQgYXBpKCJHRVQiLCAiL2FwaS9hZG1pbi9zdGFmZiIpOwogIHNldFNjcmVlbigic3RhZmZVc2VycyIpOwp9CmFzeW5jIGZ1bmN0aW9uIGFkZFN0YWZmVXNlcigpIHsKICBjb25zdCB1c2VybmFtZSA9IGRvY3VtZW50LmdldEVsZW1lbnRCeUlkKCJuZXdTdGFmZlVzZXJuYW1lIikudmFsdWUudHJpbSgpOwogIGNvbnN0IHBhc3N3b3JkID0gZG9jdW1lbnQuZ2V0RWxlbWVudEJ5SWQoIm5ld1N0YWZmUGFzc3dvcmQiKS52YWx1ZTsKICBjb25zdCByb2xlID0gZG9jdW1lbnQuZ2V0RWxlbWVudEJ5SWQoIm5ld1N0YWZmUm9sZSIpLnZhbHVlOwogIHRyeSB7IGF3YWl0IGFwaSgiUE9TVCIsICIvYXBpL2FkbWluL3N0YWZmIiwgeyB1c2VybmFtZSwgcGFzc3dvcmQsIHJvbGUgfSk7IHN0YXRlLmFkbWluLnN0YWZmTGlzdCA9IGF3YWl0IGFwaSgiR0VUIiwgIi9hcGkvYWRtaW4vc3RhZmYiKTsgc2hvd1RvYXN0KCLaqdin2LHZhdmG2K8g2KfYttin2YHZhyDYtNivIik7IHJlbmRlcigpOyB9CiAgY2F0Y2ggKGUpIHsgc3RhdGUuZXJyb3JNc2cgPSBlLm1lc3NhZ2U7IHJlbmRlcigpOyB9Cn0KYXN5bmMgZnVuY3Rpb24gdG9nZ2xlQmxvY2tTdGFmZihpZCwgYmxvY2tlZCkgewogIHRyeSB7IGF3YWl0IGFwaSgiUFVUIiwgYC9hcGkvYWRtaW4vc3RhZmYvJHtpZH0vYmxvY2tgLCB7IGJsb2NrZWQgfSk7IHN0YXRlLmFkbWluLnN0YWZmTGlzdCA9IGF3YWl0IGFwaSgiR0VUIiwgIi9hcGkvYWRtaW4vc3RhZmYiKTsgcmVuZGVyKCk7IH0KICBjYXRjaCAoZSkgeyBzdGF0ZS5lcnJvck1zZyA9IGUubWVzc2FnZTsgcmVuZGVyKCk7IH0KfQphc3luYyBmdW5jdGlvbiBkZWxldGVTdGFmZlVzZXIoaWQpIHsKICB0cnkgeyBhd2FpdCBhcGkoIkRFTEVURSIsIGAvYXBpL2FkbWluL3N0YWZmLyR7aWR9YCk7IHN0YXRlLmFkbWluLnN0YWZmTGlzdCA9IHN0YXRlLmFkbWluLnN0YWZmTGlzdC5maWx0ZXIoKHUpID0+IHUuaWQgIT09IE51bWJlcihpZCkpOyByZW5kZXIoKTsgfQogIGNhdGNoIChlKSB7IHN0YXRlLmVycm9yTXNnID0gZS5tZXNzYWdlOyByZW5kZXIoKTsgfQp9Cgphc3luYyBmdW5jdGlvbiBnb1ByRGFzaGJvYXJkKCkgeyBzdGF0ZS5hZG1pbi5wciA9IGF3YWl0IGFwaSgiR0VUIiwgIi9hcGkvYWRtaW4vZGFzaGJvYXJkL3ByIik7IHNldFNjcmVlbigicHJEYXNoYm9hcmQiKTsgfQphc3luYyBmdW5jdGlvbiBnb0NybURhc2hib2FyZCgpIHsgc3RhdGUuYWRtaW4uY3JtID0gYXdhaXQgYXBpKCJHRVQiLCAiL2FwaS9hZG1pbi9kYXNoYm9hcmQvY3JtIik7IHNldFNjcmVlbigiY3JtRGFzaGJvYXJkIik7IH0KYXN5bmMgZnVuY3Rpb24gZ29BY3Rpdml0eUxvZygpIHsgc3RhdGUuYWRtaW4uYWN0aXZpdHlMb2cgPSBhd2FpdCBhcGkoIkdFVCIsICIvYXBpL2FkbWluL2FjdGl2aXR5LWxvZyIpOyBzZXRTY3JlZW4oImFjdGl2aXR5TG9nIik7IH0KZnVuY3Rpb24gcHJpbnRSZXBvcnQoKSB7IHdpbmRvdy5wcmludCgpOyB9CgovKiA9PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT0KICAg2K/bjNiz2b7ahtixINqp2YTbjNqpCiAgID09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PSAqLwpmdW5jdGlvbiBhY3Rpb25TZXRGb3JtKGtleSwgdmFsdWUpIHsKICBsZXQgdiA9IHZhbHVlOwogIGlmICh2ID09PSAidHJ1ZSIpIHYgPSB0cnVlOyBlbHNlIGlmICh2ID09PSAiZmFsc2UiKSB2ID0gZmFsc2U7CiAgZWxzZSBpZiAoL15bMS01XSQvLnRlc3QodmFsdWUpKSB2ID0gTnVtYmVyKHZhbHVlKTsKICBzdGF0ZS5mb3JtW2tleV0gPSB2OwogIHJlbmRlcigpOwp9Cgpkb2N1bWVudC5hZGRFdmVudExpc3RlbmVyKCJjbGljayIsIGFzeW5jIChlKSA9PiB7CiAgY29uc3QgYnRuID0gZS50YXJnZXQuY2xvc2VzdCgiW2RhdGEtYWN0aW9uXSIpOwogIGlmICghYnRuIHx8IGJ0bi5kaXNhYmxlZCkgcmV0dXJuOwogIGNvbnN0IGFjdGlvbiA9IGJ0bi5kYXRhc2V0LmFjdGlvbjsKICBjb25zdCBkYXRhID0gYnRuLmRhdGFzZXQ7CiAgdHJ5IHsKICAgIHN3aXRjaCAoYWN0aW9uKSB7CiAgICAgIGNhc2UgImdvTGFuZGluZyI6IHNldFNjcmVlbigibGFuZGluZyIpOyBicmVhazsKICAgICAgY2FzZSAiZ29Eb25vckF1dGgiOiBnb0Rvbm9yQXV0aCgpOyBicmVhazsKICAgICAgY2FzZSAiZ29TdGFmZkxvZ2luIjogYXdhaXQgZ29TdGFmZkxvZ2luQWN0aW9uKCk7IGJyZWFrOwogICAgICBjYXNlICJyZXF1ZXN0T3RwIjogYXdhaXQgcmVxdWVzdE90cCgpOyBicmVhazsKICAgICAgY2FzZSAidmVyaWZ5T3RwIjogYXdhaXQgdmVyaWZ5T3RwKCk7IGJyZWFrOwogICAgICBjYXNlICJzdWJtaXRSZWdpc3RlciI6IGF3YWl0IHN1Ym1pdFJlZ2lzdGVyKCk7IGJyZWFrOwogICAgICBjYXNlICJzdWJtaXRTdXJ2ZXkiOiBhd2FpdCBzdWJtaXRTdXJ2ZXkoKTsgYnJlYWs7CiAgICAgIGNhc2UgImRvbm9yTG9nb3V0IjogZG9ub3JMb2dvdXRBY3Rpb24oKTsgYnJlYWs7CiAgICAgIGNhc2UgImJhY2tUb0Rvbm9ySG9tZSI6IGJhY2tUb0Rvbm9ySG9tZSgpOyBicmVhazsKICAgICAgY2FzZSAiZ29Cb29rQXBwb2ludG1lbnQiOiBnb0Jvb2tBcHBvaW50bWVudCgpOyBicmVhazsKICAgICAgY2FzZSAibG9hZFNsb3RzIjogYXdhaXQgbG9hZFNsb3RzKCk7IGJyZWFrOwogICAgICBjYXNlICJwaWNrU2xvdCI6IHBpY2tTbG90KGRhdGEudGltZSk7IGJyZWFrOwogICAgICBjYXNlICJzdWJtaXRCb29raW5nIjogYXdhaXQgc3VibWl0Qm9va2luZygpOyBicmVhazsKICAgICAgY2FzZSAiY2FuY2VsQXBwb2ludG1lbnQiOiBhd2FpdCBjYW5jZWxBcHBvaW50bWVudChOdW1iZXIoZGF0YS5pZCkpOyBicmVhazsKICAgICAgY2FzZSAiYWNjZXB0UmVzY2hlZHVsZSI6IGF3YWl0IGFjY2VwdFJlc2NoZWR1bGUoTnVtYmVyKGRhdGEuaWQpKTsgYnJlYWs7CiAgICAgIGNhc2UgIm9wZW5Gb2xsb3dVcCI6IG9wZW5Gb2xsb3dVcChOdW1iZXIoZGF0YS5hcHB0KSwgTnVtYmVyKGRhdGEuZGF5KSk7IGJyZWFrOwogICAgICBjYXNlICJzdWJtaXRGb2xsb3dVcCI6IGF3YWl0IHN1Ym1pdEZvbGxvd1VwKCk7IGJyZWFrOwogICAgICBjYXNlICJ0b2dnbGVDYWxsYmFjayI6IHN0YXRlLmZvcm0uY2FsbGJhY2tSZXF1ZXN0ZWQgPSAhc3RhdGUuZm9ybS5jYWxsYmFja1JlcXVlc3RlZDsgcmVuZGVyKCk7IGJyZWFrOwogICAgICBjYXNlICJzZXRGb3JtIjogYWN0aW9uU2V0Rm9ybShkYXRhLmtleSwgZGF0YS52YWx1ZSk7IGJyZWFrOwoKICAgICAgY2FzZSAic3RhZmZMb2dpblN1Ym1pdCI6IGF3YWl0IHN0YWZmTG9naW5TdWJtaXQoKTsgYnJlYWs7CiAgICAgIGNhc2UgInN0YWZmTG9nb3V0IjogYXdhaXQgc3RhZmZMb2dvdXRBY3Rpb24oKTsgYnJlYWs7CiAgICAgIGNhc2UgImdvQ2hhbmdlUGFzc3dvcmQiOiBzdGF0ZS5mb3JjZWRQd0NoYW5nZSA9IGZhbHNlOyBzZXRTY3JlZW4oImNoYW5nZVBhc3N3b3JkIik7IGJyZWFrOwogICAgICBjYXNlICJzdWJtaXRDaGFuZ2VQYXNzd29yZCI6IGF3YWl0IHN1Ym1pdENoYW5nZVBhc3N3b3JkKCk7IGJyZWFrOwogICAgICBjYXNlICJnb1N0YWZmRGFzaGJvYXJkIjogYXdhaXQgZ29TdGFmZkRhc2hib2FyZEFjdGlvbigpOyBicmVhazsKICAgICAgY2FzZSAiZ29Ob3RpZkNlbnRlciI6IGF3YWl0IGdvTm90aWZDZW50ZXIoKTsgYnJlYWs7CiAgICAgIGNhc2UgImdvRG9ub3JMaXN0IjogYXdhaXQgZ29Eb25vckxpc3QoKTsgYnJlYWs7CiAgICAgIGNhc2UgInNlYXJjaERvbm9ycyI6IGF3YWl0IHNlYXJjaERvbm9ycygpOyBicmVhazsKICAgICAgY2FzZSAiZXhwb3J0Q3N2IjogZXhwb3J0Q3N2KCk7IGJyZWFrOwogICAgICBjYXNlICJvcGVuRG9ub3JCeVBob25lIjogYXdhaXQgb3BlbkRvbm9yQnlQaG9uZShkYXRhLnBob25lKTsgYnJlYWs7CiAgICAgIGNhc2UgImFwcHJvdmVMYWIiOiBhd2FpdCBhcHByb3ZlTGFiKCk7IGJyZWFrOwogICAgICBjYXNlICJibG9ja0Rvbm9yIjogYXdhaXQgYmxvY2tEb25vcigpOyBicmVhazsKICAgICAgY2FzZSAidW5ibG9ja0Rvbm9yIjogYXdhaXQgdW5ibG9ja0Rvbm9yKCk7IGJyZWFrOwogICAgICBjYXNlICJkZWxldGVEb25vciI6IGF3YWl0IGRlbGV0ZURvbm9yKCk7IGJyZWFrOwogICAgICBjYXNlICJkZWxldGVTdXJ2ZXkiOiBhd2FpdCBkZWxldGVTdXJ2ZXkoKTsgYnJlYWs7CiAgICAgIGNhc2UgImFkZE5vdGUiOiBhd2FpdCBhZGROb3RlKCk7IGJyZWFrOwogICAgICBjYXNlICJkZWxldGVOb3RlIjogYXdhaXQgZGVsZXRlTm90ZShOdW1iZXIoZGF0YS5pZCkpOyBicmVhazsKICAgICAgY2FzZSAiYWRkUmVtaW5kZXIiOiBhd2FpdCBhZGRSZW1pbmRlcigpOyBicmVhazsKICAgICAgY2FzZSAibWFya1JlbWluZGVyRG9uZSI6IGF3YWl0IG1hcmtSZW1pbmRlckRvbmUoTnVtYmVyKGRhdGEuaWQpKTsgYnJlYWs7CiAgICAgIGNhc2UgImNvbmZpcm1BcHBvaW50bWVudCI6IGF3YWl0IGNvbmZpcm1BcHBvaW50bWVudChOdW1iZXIoZGF0YS5pZCkpOyBicmVhazsKICAgICAgY2FzZSAicHJvcG9zZVJlc2NoZWR1bGUiOiBhd2FpdCBwcm9wb3NlUmVzY2hlZHVsZShOdW1iZXIoZGF0YS5pZCkpOyBicmVhazsKICAgICAgY2FzZSAiY2FuY2VsQXBwdEFkbWluIjogYXdhaXQgY2FuY2VsQXBwdEFkbWluKE51bWJlcihkYXRhLmlkKSk7IGJyZWFrOwogICAgICBjYXNlICJvcGVuT3V0Y29tZUZvcm0iOiBvcGVuT3V0Y29tZUZvcm0oTnVtYmVyKGRhdGEuaWQpKTsgYnJlYWs7CiAgICAgIGNhc2UgInRvZ2dsZU91dGNvbWVBdHRlbmRlZCI6IHRvZ2dsZU91dGNvbWVBdHRlbmRlZCgpOyBicmVhazsKICAgICAgY2FzZSAic3VibWl0T3V0Y29tZSI6IGF3YWl0IHN1Ym1pdE91dGNvbWUoKTsgYnJlYWs7CiAgICAgIGNhc2UgImNyZWF0ZUFwcHRGb3JEb25vciI6IGF3YWl0IGNyZWF0ZUFwcHRGb3JEb25vcigpOyBicmVhazsKICAgICAgY2FzZSAiYmFja1RvRG9ub3JEZXRhaWwiOiBiYWNrVG9Eb25vckRldGFpbCgpOyBicmVhazsKICAgICAgY2FzZSAiZ29BcHBvaW50bWVudHMiOiBhd2FpdCBnb0FwcG9pbnRtZW50cygpOyBicmVhazsKICAgICAgY2FzZSAibG9hZEFkbWluU2xvdHMiOiBhd2FpdCBsb2FkQWRtaW5TbG90cygpOyBicmVhazsKICAgICAgY2FzZSAiZ29TZXR0aW5ncyI6IGF3YWl0IGdvU2V0dGluZ3MoKTsgYnJlYWs7CiAgICAgIGNhc2UgInRvZ2dsZUNsb3NlZERheSI6IHRvZ2dsZUNsb3NlZERheShOdW1iZXIoZGF0YS5kYXkpKTsgYnJlYWs7CiAgICAgIGNhc2UgInNldEFwcG9pbnRtZW50TW9kZSI6IHNldEFwcG9pbnRtZW50TW9kZShkYXRhLm1vZGUpOyBicmVhazsKICAgICAgY2FzZSAic2F2ZVNldHRpbmdzIjogYXdhaXQgc2F2ZVNldHRpbmdzKCk7IGJyZWFrOwogICAgICBjYXNlICJzYXZlU21zVGVtcGxhdGVzIjogYXdhaXQgc2F2ZVNtc1RlbXBsYXRlcygpOyBicmVhazsKICAgICAgY2FzZSAiZ29TdGFmZlVzZXJzIjogYXdhaXQgZ29TdGFmZlVzZXJzKCk7IGJyZWFrOwogICAgICBjYXNlICJhZGRTdGFmZlVzZXIiOiBhd2FpdCBhZGRTdGFmZlVzZXIoKTsgYnJlYWs7CiAgICAgIGNhc2UgInRvZ2dsZUJsb2NrU3RhZmYiOiBhd2FpdCB0b2dnbGVCbG9ja1N0YWZmKE51bWJlcihkYXRhLmlkKSwgZGF0YS5ibG9ja2VkID09PSAidHJ1ZSIpOyBicmVhazsKICAgICAgY2FzZSAiZGVsZXRlU3RhZmZVc2VyIjogYXdhaXQgZGVsZXRlU3RhZmZVc2VyKE51bWJlcihkYXRhLmlkKSk7IGJyZWFrOwogICAgICBjYXNlICJnb1ByRGFzaGJvYXJkIjogYXdhaXQgZ29QckRhc2hib2FyZCgpOyBicmVhazsKICAgICAgY2FzZSAiZ29Dcm1EYXNoYm9hcmQiOiBhd2FpdCBnb0NybURhc2hib2FyZCgpOyBicmVhazsKICAgICAgY2FzZSAiZ29BY3Rpdml0eUxvZyI6IGF3YWl0IGdvQWN0aXZpdHlMb2coKTsgYnJlYWs7CiAgICAgIGNhc2UgInByaW50UmVwb3J0IjogcHJpbnRSZXBvcnQoKTsgYnJlYWs7CiAgICAgIGNhc2UgImNoYW5nZVN0YXR1cyI6IGJyZWFrOyAvLyDYr9ixINix2YjbjNiv2KfYryBjaGFuZ2Ug2YXYr9uM2LHbjNiqINmF24zigIzYtNmHCiAgICB9CiAgfSBjYXRjaCAoZXJyKSB7IHN0YXRlLmVycm9yTXNnID0gZXJyLm1lc3NhZ2U7IHJlbmRlcigpOyB9Cn0pOwoKZG9jdW1lbnQuYWRkRXZlbnRMaXN0ZW5lcigiY2hhbmdlIiwgYXN5bmMgKGUpID0+IHsKICBpZiAoZS50YXJnZXQuZGF0YXNldCAmJiBlLnRhcmdldC5kYXRhc2V0LmFjdGlvbiA9PT0gImNoYW5nZVN0YXR1cyIpIHsKICAgIGF3YWl0IGNoYW5nZVN0YXR1c0FjdGlvbihlLnRhcmdldC52YWx1ZSk7CiAgfQp9KTsKCi8qID09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PQogICDYsdin2YfigIzYp9mG2K/Yp9iy24wg2KfZiNmE24zZhwogICA9PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT0gKi8KKGFzeW5jIGZ1bmN0aW9uIGluaXQoKSB7CiAgdHJ5IHsgc3RhdGUuc3RhZmYgPSBhd2FpdCBhcGkoIkdFVCIsICIvYXBpL3N0YWZmLWF1dGgvbWUiKTsgfSBjYXRjaCAoZSkgeyBzdGF0ZS5zdGFmZiA9IG51bGw7IH0KICByZW5kZXIoKTsKfSkoKTsK", "base64").toString("utf8");
app.get("/app.js", (req, res) => { res.type("application/javascript").send(APP_JS); });
app.get("/", (req, res) => { res.type("html").send(INDEX_HTML); });
app.get("*", (req, res) => { res.type("html").send(INDEX_HTML); });

/* ============================================================
   بخش ۱۱: ساخت خودکار حساب مدیر در اولین اجرا
   ============================================================ */
const DEFAULT_ADMIN_USERNAME = "admin";
const DEFAULT_ADMIN_PASSWORD = "admin1234";
function bootstrapAdmin() {
  const username = process.env.ADMIN_USERNAME || DEFAULT_ADMIN_USERNAME;
  const password = process.env.ADMIN_PASSWORD || DEFAULT_ADMIN_PASSWORD;
  const usingDefaults = !process.env.ADMIN_USERNAME || !process.env.ADMIN_PASSWORD;
  mutate((db) => {
    if (db.staff.length > 0) return;
    db.staff.push({ id: db.nextIds.staff++, username, passwordHash: bcrypt.hashSync(password, 12), role: "admin", mustChangePassword: true, blocked: false, createdAt: new Date().toISOString() });
    if (usingDefaults) console.warn(`⚠️  از مقادیر پیش‌فرض استفاده شد -> نام کاربری: ${username} | رمز: ${password} — همین الان از داخل برنامه عوضش کنید.`);
    else console.log(`✅ حساب مدیر اولیه ساخته شد (نام کاربری: ${username}).`);
  });
}
bootstrapAdmin();

app.listen(PORT, () => console.log(`🩸 سرور CRM مرکز اهدا پلاسما روی پورت ${PORT} در حال اجراست`));

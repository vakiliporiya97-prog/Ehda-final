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

function postWebhook(url, payload) {
  return new Promise((resolve) => {
    try {
      const body = JSON.stringify(payload);
      const u = new URL(url);
      const req = https.request(
        { hostname: u.hostname, path: u.pathname + u.search, method: "POST", headers: { "Content-Type": "application/json", "Content-Length": Buffer.byteLength(body) } },
        (res) => { res.on("data", () => {}); res.on("end", () => resolve(true)); }
      );
      req.on("error", () => resolve(false));
      req.write(body);
      req.end();
    } catch (e) { resolve(false); }
  });
}

/** ارسال/ثبت یک نوتیفیکیشن برای یک اهداکننده بر اساس یکی از قالب‌های پیامک */
async function notify(db, donor, templateKey, extraVars = {}) {
  const tpl = db.settings.smsTemplates[templateKey] || "";
  const text = renderTemplate(tpl, { name: `${donor.firstName} ${donor.lastName}`, centerName: db.settings.centerName, ...extraVars });

  let delivered = false;
  const webhook = process.env.SMS_WEBHOOK_URL;
  if (webhook) {
    delivered = await postWebhook(webhook, { phone: donor.phone, text });
  }

  mutate((d2) => {
    const donorRef = d2.donors.find((x) => x.id === donor.id);
    d2.notifications.push({
      id: d2.nextIds.notification++,
      donorId: donor.id,
      templateKey,
      text,
      createdAt: new Date().toISOString(),
      delivered,
    });
  });

  return { text, delivered };
}

function logActivity(db, actorUsername, action, detail) {
  mutate((d2) => {
    d2.activityLog.push({ id: d2.nextIds.activity++, actorUsername, action, detail, createdAt: new Date().toISOString() });
  });
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
      styleSrc: ["'self'", "'unsafe-inline'", "https://cdn.tailwindcss.com"],
      scriptSrc: ["'self'", "'unsafe-inline'", "https://cdn.tailwindcss.com"],
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

donorAuthRouter.post("/request-otp", (req, res) => {
  const phone = normalizePhone(req.body && req.body.phone);
  if (phone.length < 10) return res.status(400).json({ error: "شماره موبایل معتبر نیست" });
  const code = generateOtp(phone);
  const webhookConfigured = !!process.env.SMS_WEBHOOK_URL;
  // اگه سرویس پیامک وصل نشده، کد رو مستقیم برمی‌گردونیم تا بشه تست کرد (حالت دمو)
  res.json({ ok: true, demoCode: webhookConfigured ? undefined : code });
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
const INDEX_HTML = Buffer.from("PCFET0NUWVBFIGh0bWw+CjxodG1sIGxhbmc9ImZhIiBkaXI9InJ0bCI+CjxoZWFkPgo8bWV0YSBjaGFyc2V0PSJVVEYtOCIgLz4KPG1ldGEgbmFtZT0idmlld3BvcnQiIGNvbnRlbnQ9IndpZHRoPWRldmljZS13aWR0aCwgaW5pdGlhbC1zY2FsZT0xLjAsIG1heGltdW0tc2NhbGU9MSIgLz4KPHRpdGxlPtmF2LHaqdiyINin2YfYr9inINm+2YTYp9iz2YXYpyDZhtmI24zZhiDZvtmE2KfYs9mF2Kcg2b7ZiNix2Kcg2K/Yp9ix2Yg8L3RpdGxlPgo8c2NyaXB0IHNyYz0iaHR0cHM6Ly9jZG4udGFpbHdpbmRjc3MuY29tIj48L3NjcmlwdD4KPHN0eWxlPgogIGJvZHkgeyBmb250LWZhbWlseTogVGFob21hLCAiU2Vnb2UgVUkiLCBBcmlhbCwgc2Fucy1zZXJpZjsgfQogIC5mYWRlLWluIHsgYW5pbWF0aW9uOiBmYWRlSW4gLjJzIGVhc2U7IH0KICBAa2V5ZnJhbWVzIGZhZGVJbiB7IGZyb20geyBvcGFjaXR5OiAwOyB0cmFuc2Zvcm06IHRyYW5zbGF0ZVkoNnB4KTsgfSB0byB7IG9wYWNpdHk6IDE7IHRyYW5zZm9ybTogdHJhbnNsYXRlWSgwKTsgfSB9CiAgQG1lZGlhIHByaW50IHsgLm5vLXByaW50IHsgZGlzcGxheTogbm9uZSAhaW1wb3J0YW50OyB9IH0KPC9zdHlsZT4KPC9oZWFkPgo8Ym9keSBjbGFzcz0iYmctc3RvbmUtNTAgbWluLWgtc2NyZWVuIj4KICA8ZGl2IGlkPSJhcHAiIGNsYXNzPSJtaW4taC1zY3JlZW4iPjwvZGl2PgogIDxzY3JpcHQgc3JjPSIvYXBwLmpzIj48L3NjcmlwdD4KPC9ib2R5Pgo8L2h0bWw+Cg==", "base64").toString("utf8");
const APP_JS = Buffer.from("LyogPT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09CiAgINmF2LHaqdiyINin2YfYr9inINm+2YTYp9iz2YXYpyDZhtmI24zZhiDZvtmE2KfYs9mF2Kcg2b7ZiNix2Kcg2K/Yp9ix2Ygg4oCUINm+2YbZhCBDUk0KICAgPT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09ICovCgphc3luYyBmdW5jdGlvbiBhcGkobWV0aG9kLCB1cmwsIGJvZHkpIHsKICBjb25zdCByZXMgPSBhd2FpdCBmZXRjaCh1cmwsIHsKICAgIG1ldGhvZCwgaGVhZGVyczogeyAiQ29udGVudC1UeXBlIjogImFwcGxpY2F0aW9uL2pzb24iIH0sIGNyZWRlbnRpYWxzOiAic2FtZS1vcmlnaW4iLAogICAgYm9keTogYm9keSAhPT0gdW5kZWZpbmVkID8gSlNPTi5zdHJpbmdpZnkoYm9keSkgOiB1bmRlZmluZWQsCiAgfSk7CiAgbGV0IGRhdGEgPSBudWxsOwogIHRyeSB7IGRhdGEgPSBhd2FpdCByZXMuanNvbigpOyB9IGNhdGNoIChlKSB7fQogIGlmICghcmVzLm9rKSB0aHJvdyBuZXcgRXJyb3IoKGRhdGEgJiYgZGF0YS5lcnJvcikgfHwgItiu2LfYp9uMINmG2KfYtNmG2KfYrtiq2Ycg2LPYsdmI2LEiKTsKICByZXR1cm4gZGF0YTsKfQoKZnVuY3Rpb24gZXNjKHN0cikgeyBjb25zdCBkID0gZG9jdW1lbnQuY3JlYXRlRWxlbWVudCgiZGl2Iik7IGQudGV4dENvbnRlbnQgPSBzdHIgPT0gbnVsbCA/ICIiIDogU3RyaW5nKHN0cik7IHJldHVybiBkLmlubmVySFRNTDsgfQoKY29uc3QgRkFfTU9OVEhTID0gWyLZgdix2YjYsdiv24zZhiIsItin2LHYr9uM2KjZh9i02KoiLCLYrtix2K/Yp9ivIiwi2KrbjNixIiwi2YXYsdiv2KfYryIsIti02YfYsduM2YjYsSIsItmF2YfYsSIsItii2KjYp9mGIiwi2KLYsNixIiwi2K/bjCIsItio2YfZhdmGIiwi2KfYs9mB2YbYryJdOwpjb25zdCBGQV9XRUVLREFZUyA9IFsi24zaqdi02YbYqNmHIiwi2K/ZiNi02YbYqNmHIiwi2LPZh+KAjNi02YbYqNmHIiwi2obZh9in2LHYtNmG2KjZhyIsItm+2YbYrNi02YbYqNmHIiwi2KzZhdi52YciLCLYtNmG2KjZhyJdOwpmdW5jdGlvbiBmYURpZ2l0cyhuKSB7IGNvbnN0IG1hcD17MDoi27AiLDE6ItuxIiwyOiLbsiIsMzoi27MiLDQ6Itu0Iiw1OiLbtSIsNjoi27YiLDc6Itu3Iiw4OiLbuCIsOToi27kifTsgcmV0dXJuIFN0cmluZyhuKS5yZXBsYWNlKC9bMC05XS9nLChjKT0+bWFwW2NdKTsgfQpmdW5jdGlvbiBnVG9KYWxhbGkoZ3ksIGdtLCBnZCkgewogIGNvbnN0IGdfZF9tPVswLDMxLDU5LDkwLDEyMCwxNTEsMTgxLDIxMiwyNDMsMjczLDMwNCwzMzRdOwogIGxldCBneTIgPSBnbT4yP2d5KzE6Z3k7CiAgbGV0IGRheXMgPSAzNTU2NjYrMzY1Kmd5K01hdGguZmxvb3IoKGd5MiszKS80KS1NYXRoLmZsb29yKChneTIrOTkpLzEwMCkrTWF0aC5mbG9vcigoZ3kyKzM5OSkvNDAwKStnZCtnX2RfbVtnbS0xXTsKICBsZXQgankgPSAtMTU5NSszMypNYXRoLmZsb29yKGRheXMvMTIwNTMpOyBkYXlzJT0xMjA1MzsKICBqeSArPSA0Kk1hdGguZmxvb3IoZGF5cy8xNDYxKTsgZGF5cyU9MTQ2MTsKICBpZiAoZGF5cz4zNjUpeyBqeSs9TWF0aC5mbG9vcigoZGF5cy0xKS8zNjUpOyBkYXlzPShkYXlzLTEpJTM2NTsgfQogIGxldCBqbSxqZDsKICBpZiAoZGF5czwxODYpeyBqbT0xK01hdGguZmxvb3IoZGF5cy8zMSk7IGpkPTErKGRheXMlMzEpOyB9IGVsc2UgeyBqbT03K01hdGguZmxvb3IoKGRheXMtMTg2KS8zMCk7IGpkPTErKChkYXlzLTE4NiklMzApOyB9CiAgcmV0dXJuIFtqeSxqbSxqZF07Cn0KZnVuY3Rpb24gamFsYWxpUGFydHMoZGF0ZUlucHV0KSB7CiAgY29uc3QgZCA9IG5ldyBEYXRlKGRhdGVJbnB1dCk7CiAgY29uc3QgW2p5LGptLGpkXSA9IGdUb0phbGFsaShkLmdldEZ1bGxZZWFyKCksIGQuZ2V0TW9udGgoKSsxLCBkLmdldERhdGUoKSk7CiAgcmV0dXJuIHsgeWVhcjoganksIG1vbnRoOiBqbSwgZGF5OiBqZCwgbW9udGhOYW1lOiBGQV9NT05USFNbam0tMV0sIHdlZWtkYXk6IEZBX1dFRUtEQVlTW2QuZ2V0RGF5KCldLCBfZDogZCB9Owp9CmZ1bmN0aW9uIGZtdERhdGUoZGF0ZUlucHV0KSB7IGlmICghZGF0ZUlucHV0KSByZXR1cm4gIi0iOyBjb25zdCBqPWphbGFsaVBhcnRzKGRhdGVJbnB1dCk7IHJldHVybiBgJHtqLndlZWtkYXl9ICR7ZmFEaWdpdHMoai5kYXkpfSAke2oubW9udGhOYW1lfSAke2ZhRGlnaXRzKGoueWVhcil9YDsgfQpmdW5jdGlvbiBmbXREYXRlU2hvcnQoZGF0ZUlucHV0KSB7IGlmICghZGF0ZUlucHV0KSByZXR1cm4gIi0iOyBjb25zdCBqPWphbGFsaVBhcnRzKGRhdGVJbnB1dCk7IHJldHVybiBgJHtmYURpZ2l0cyhqLmRheSl9ICR7ai5tb250aE5hbWV9ICR7ZmFEaWdpdHMoai55ZWFyKX1gOyB9CmZ1bmN0aW9uIGZtdERhdGVUaW1lKGRhdGVJbnB1dCkgeyBpZiAoIWRhdGVJbnB1dCkgcmV0dXJuICItIjsgY29uc3Qgaj1qYWxhbGlQYXJ0cyhkYXRlSW5wdXQpOyBjb25zdCBoaD1TdHJpbmcoai5fZC5nZXRIb3VycygpKS5wYWRTdGFydCgyLCIwIik7IGNvbnN0IG1tPVN0cmluZyhqLl9kLmdldE1pbnV0ZXMoKSkucGFkU3RhcnQoMiwiMCIpOyByZXR1cm4gYCR7ZmFEaWdpdHMoai5kYXkpfSAke2oubW9udGhOYW1lfdiMICR7ZmFEaWdpdHMoaGgpfToke2ZhRGlnaXRzKG1tKX1gOyB9CmZ1bmN0aW9uIHRvZGF5SVNPRGF0ZSgpIHsgY29uc3QgZD1uZXcgRGF0ZSgpOyByZXR1cm4gYCR7ZC5nZXRGdWxsWWVhcigpfS0ke1N0cmluZyhkLmdldE1vbnRoKCkrMSkucGFkU3RhcnQoMiwiMCIpfS0ke1N0cmluZyhkLmdldERhdGUoKSkucGFkU3RhcnQoMiwiMCIpfWA7IH0KCmNvbnN0IFdFRUtEQVlfTEFCRUxTID0gWyLbjNqp2LTZhtio2YciLCLYr9mI2LTZhtio2YciLCLYs9mH4oCM2LTZhtio2YciLCLahtmH2KfYsdi02YbYqNmHIiwi2b7Zhtis2LTZhtio2YciLCLYrNmF2LnZhyIsIti02YbYqNmHIl07CmNvbnN0IFJFRkVSUkFMX09QVElPTlMgPSBbItix2YjYp9io2Lcg2LnZhdmI2YXbjCIsItin24zZhtiz2KrYp9qv2LHYp9mFIiwi2YXYudix2YHbjCDYr9mI2LPYqtin2YYg2Ygg2KLYtNmG2KfbjNin2YYiLCLYqtio2YTbjNi62KfYqiDZhdit24zYt9uMIiwi2KzYs9iq2KzZiNuMINin24zZhtiq2LHZhtiqIiwi2YXYsdin2KzYudmHINmC2KjZhNuMIiwi2LPYp9uM2LEiXTsKY29uc3QgU1VSVkVZX0NBVEVHT1JJRVMgPSBbCiAgWyJzZWN1cml0eUJlaGF2aW9yIiwgItmG2K3ZiNmH4oCM24wg2KjYsdiu2YjYsdivINit2LHYp9iz2KoiXSwKICBbInJlY2VwdGlvbkJlaGF2aW9yIiwgItmG2K3ZiNmH4oCM24wg2KjYsdiu2YjYsdivINm+2LDbjNix2LQiXSwKICBbImRvY3RvckJlaGF2aW9yIiwgItix2YHYqtin2LEg2b7Ysti02qkiXSwKICBbIm51cnNlQmVoYXZpb3IiLCAi2LHZgdiq2KfYsSDZvtix2LPYqtin2LHYp9mGIl0sCiAgWyJzdGFmZkJlaGF2aW9yIiwgItix2YHYqtin2LEg2LPYp9uM2LEg2qnYp9ix2qnZhtin2YYiXSwKICBbIm9yZGVyU3BlZWQiLCAi2YbYuNmFINmIINiz2LHYudiqINin2YbYrNin2YUg2qnYp9ixIl0sCiAgWyJjbGVhbmxpbmVzcyIsICLYqtmF24zYstuMINmIINmG2LjYp9mB2Kog2YXYsdqp2LIiXSwKICBbImFtYmlhbmNlIiwgItii2LHYp9mF2LQg2Ygg2YHYttin24wg2YXYrduM2LciXSwKICBbIm92ZXJhbGxTYXRpc2ZhY3Rpb24iLCAi2YXbjNiy2KfZhiDYsdi22KfbjNiqINqp2YTbjCDYp9iyINin2YjZhNuM2YYg2YXYsdin2KzYudmHIl0sCl07CmNvbnN0IFNUQVRVU19MQUJFTFMgPSB7CiAgcmVnaXN0ZXJlZDogItir2KjYquKAjNmG2KfZhSDYp9mI2YTbjNmHIiwgYXdhaXRpbmdfbGFiOiAi2YXZhtiq2LjYsSDYrNmI2KfYqCDYotiy2YXYp9uM2LQiLCByZWFkeTogItii2YXYp9iv2Ycg2KrYuduM24zZhiDZhtmI2KjYqiIsCiAgYm9va2VkOiAi2YbZiNio2Kog2LHYstix2Ygg2LTYr9mHIiwgdmlzaXRlZDogItmF2LHYp9is2LnZhyDaqdix2K8iLCBkb25hdGVkOiAi2KfZh9iv2Kcg2KfZhtis2KfZhSDYtNivIiwKICBuZWVkc19mb2xsb3d1cDogItmG24zYp9iy2YXZhtivINm+24zar9uM2LHbjCIsIHVucmVzcG9uc2l2ZTogIti52K/ZhSDZvtin2LPYrtqv2YjbjNuMIiwgaW5hY3RpdmU6ICLYutuM2LHZgdi52KfZhCIsIGJsb2NrZWQ6ICLZhdiz2K/ZiNivINi02K/ZhyIsCn07CmNvbnN0IFJFTUlOREVSX1RZUEVTID0gWyLYqtmF2KfYsyDYqtmE2YHZhtuMIiwgItin2LHYs9in2YQg2b7bjNin2YXaqSIsICLYr9i52YjYqiDYqNix2KfbjCDZhdix2KfYrNi52YciLCAi2b7bjNqv24zYsduMINmG2KrbjNis2Ycg2KLYstmF2KfbjNi0IiwgItio2LHYsdiz24wg2YjYtti524zYqiDYs9mE2KfZhdiqIl07Cgpjb25zdCBzdGF0ZSA9IHsKICBzY3JlZW46ICJsYW5kaW5nIiwKICB0b2FzdDogbnVsbCwgZXJyb3JNc2c6IG51bGwsCiAgZG9ub3I6IG51bGwsIGRvbm9yTm90aWZpY2F0aW9uczogW10sCiAgc3RhZmY6IG51bGwsCiAgZm9ybToge30sCiAgYWRtaW46IHsgZG9ub3JzOiBudWxsLCBxOiAiIiwgc2VsZWN0ZWRQaG9uZTogbnVsbCwgc2VsZWN0ZWREb25vcjogbnVsbCwgc2V0dGluZ3M6IG51bGwsIHN0YWZmTGlzdDogbnVsbCwgc3RhdHM6IG51bGwsIHByOiBudWxsLCBjcm06IG51bGwsIG5vdGlmQ2VudGVyOiBudWxsLCBhY3Rpdml0eUxvZzogbnVsbCwgYXBwb2ludG1lbnRzOiBudWxsLCBzbG90RGF0ZTogbnVsbCwgc2xvdHM6IG51bGwgfSwKICBmb3JjZWRQd0NoYW5nZTogZmFsc2UsCn07CgpmdW5jdGlvbiBzZXRTY3JlZW4ocywgcmVzZXRGb3JtID0gdHJ1ZSkgeyBzdGF0ZS5zY3JlZW4gPSBzOyBpZiAocmVzZXRGb3JtKSBzdGF0ZS5mb3JtID0ge307IHN0YXRlLmVycm9yTXNnID0gbnVsbDsgcmVuZGVyKCk7IHdpbmRvdy5zY3JvbGxUbygwLDApOyB9CmZ1bmN0aW9uIHNob3dUb2FzdChtc2csIHRvbmU9ImVtZXJhbGQiKSB7IHN0YXRlLnRvYXN0ID0geyBtc2csIHRvbmUgfTsgcmVuZGVyKCk7IHNldFRpbWVvdXQoKCk9Pnsgc3RhdGUudG9hc3Q9bnVsbDsgcmVuZGVyKCk7IH0sIDMyMDApOyB9CgovKiA9PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT0KICAg2YLYt9i52YfigIzZh9in24wg2LHYp9io2Lcg2qnYp9ix2KjYsduMCiAgID09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PSAqLwpmdW5jdGlvbiBDYXJkKGlubmVyLCBjbHM9IiIpIHsgcmV0dXJuIGA8ZGl2IGNsYXNzPSJiZy13aGl0ZSByb3VuZGVkLTJ4bCBzaGFkb3ctc20gYm9yZGVyIGJvcmRlci1zdG9uZS0yMDAgJHtjbHN9Ij4ke2lubmVyfTwvZGl2PmA7IH0KZnVuY3Rpb24gQmFkZ2UodGV4dCwgdG9uZT0ic2xhdGUiKSB7CiAgY29uc3QgdG9uZXMgPSB7IHNsYXRlOiJiZy1zdG9uZS0xMDAgdGV4dC1zdG9uZS02MDAiLCBhbWJlcjoiYmctYW1iZXItMTAwIHRleHQtYW1iZXItODAwIiwgZW1lcmFsZDoiYmctZW1lcmFsZC0xMDAgdGV4dC1lbWVyYWxkLTcwMCIsIHJvc2U6ImJnLXJvc2UtMTAwIHRleHQtcm9zZS03MDAiLCB0ZWFsOiJiZy10ZWFsLTEwMCB0ZXh0LXRlYWwtODAwIiB9OwogIHJldHVybiBgPHNwYW4gY2xhc3M9InB4LTIuNSBweS0xIHJvdW5kZWQtZnVsbCB0ZXh0LXhzIGZvbnQtbWVkaXVtICR7dG9uZXNbdG9uZV19Ij4ke2VzYyh0ZXh0KX08L3NwYW4+YDsKfQpmdW5jdGlvbiBQcmltYXJ5QnV0dG9uKGxhYmVsLCBhY3Rpb24sIG9wdHM9e30pIHsKICBjb25zdCBkYXRhID0gb3B0cy5kYXRhID8gT2JqZWN0LmVudHJpZXMob3B0cy5kYXRhKS5tYXAoKFtrLHZdKT0+YGRhdGEtJHtrfT0iJHtlc2Modil9ImApLmpvaW4oIiAiKSA6ICIiOwogIHJldHVybiBgPGJ1dHRvbiBkYXRhLWFjdGlvbj0iJHthY3Rpb259IiAke2RhdGF9ICR7b3B0cy5kaXNhYmxlZD8iZGlzYWJsZWQiOiIifSBjbGFzcz0idy1mdWxsIHB5LTMuNSByb3VuZGVkLXhsIGZvbnQtYm9sZCB0ZXh0LXdoaXRlIGJnLWFtYmVyLTUwMCBob3ZlcjpiZy1hbWJlci02MDAgZGlzYWJsZWQ6Ymctc3RvbmUtMzAwIHRyYW5zaXRpb24tYWxsIHNoYWRvdy1zbSAke29wdHMuY2xhc3NOYW1lfHwiIn0iPiR7ZXNjKGxhYmVsKX08L2J1dHRvbj5gOwp9CmZ1bmN0aW9uIFNtYWxsQnV0dG9uKGxhYmVsLCBhY3Rpb24sIG9wdHM9e30pIHsKICBjb25zdCBkYXRhID0gb3B0cy5kYXRhID8gT2JqZWN0LmVudHJpZXMob3B0cy5kYXRhKS5tYXAoKFtrLHZdKT0+YGRhdGEtJHtrfT0iJHtlc2Modil9ImApLmpvaW4oIiAiKSA6ICIiOwogIGNvbnN0IHRvbmUgPSBvcHRzLnRvbmUgfHwgInRlYWwiOwogIGNvbnN0IHRvbmVzID0geyB0ZWFsOiJiZy10ZWFsLTUwIHRleHQtdGVhbC04MDAgaG92ZXI6YmctdGVhbC0xMDAiLCByb3NlOiJiZy1yb3NlLTUwIHRleHQtcm9zZS03MDAgaG92ZXI6Ymctcm9zZS0xMDAiLCBlbWVyYWxkOiJiZy1lbWVyYWxkLTYwMCB0ZXh0LXdoaXRlIGhvdmVyOmJnLWVtZXJhbGQtNzAwIiwgc3RvbmU6ImJnLXN0b25lLTEwMCB0ZXh0LXN0b25lLTYwMCBob3ZlcjpiZy1zdG9uZS0yMDAiIH07CiAgcmV0dXJuIGA8YnV0dG9uIGRhdGEtYWN0aW9uPSIke2FjdGlvbn0iICR7ZGF0YX0gY2xhc3M9InB4LTMgcHktMiByb3VuZGVkLWxnIHRleHQteHMgZm9udC1ib2xkICR7dG9uZXNbdG9uZV19Ij4ke2VzYyhsYWJlbCl9PC9idXR0b24+YDsKfQpmdW5jdGlvbiBHaG9zdEJ1dHRvbihsYWJlbCwgYWN0aW9uLCBvcHRzPXt9KSB7CiAgY29uc3QgZGF0YSA9IG9wdHMuZGF0YSA/IE9iamVjdC5lbnRyaWVzKG9wdHMuZGF0YSkubWFwKChbayx2XSk9PmBkYXRhLSR7a309IiR7ZXNjKHYpfSJgKS5qb2luKCIgIikgOiAiIjsKICByZXR1cm4gYDxidXR0b24gZGF0YS1hY3Rpb249IiR7YWN0aW9ufSIgJHtkYXRhfSBjbGFzcz0idy1mdWxsIHB5LTMgcm91bmRlZC14bCBmb250LXNlbWlib2xkIHRleHQtdGVhbC04MDAgYmctdGVhbC01MCBob3ZlcjpiZy10ZWFsLTEwMCB0cmFuc2l0aW9uLWNvbG9ycyI+JHtlc2MobGFiZWwpfTwvYnV0dG9uPmA7Cn0KZnVuY3Rpb24gVG9wQmFyKHRpdGxlLCBiYWNrQWN0aW9uLCByaWdodD0iIikgewogIHJldHVybiBgPGRpdiBjbGFzcz0iZmxleCBpdGVtcy1jZW50ZXIganVzdGlmeS1iZXR3ZWVuIG1iLTUiPgogICAgJHtiYWNrQWN0aW9uID8gYDxidXR0b24gZGF0YS1hY3Rpb249IiR7YmFja0FjdGlvbn0iIGNsYXNzPSJwLTIgLW1yLTIgdGV4dC10ZWFsLTgwMCB0ZXh0LWxnIj4mIzg1OTI7PC9idXR0b24+YCA6IGA8ZGl2IGNsYXNzPSJ3LTkiPjwvZGl2PmB9CiAgICA8aDEgY2xhc3M9ImZvbnQtYm9sZCB0ZXh0LWxnIHRleHQtdGVhbC05NTAiPiR7ZXNjKHRpdGxlKX08L2gxPgogICAgPGRpdiBjbGFzcz0idy05IGZsZXgganVzdGlmeS1lbmQiPiR7cmlnaHR9PC9kaXY+CiAgPC9kaXY+YDsKfQpmdW5jdGlvbiBTY2FsZUlucHV0KG5hbWUsIGN1cnJlbnQpIHsKICBjb25zdCB2ID0gc3RhdGUuZm9ybVtuYW1lXSB8fCAwOwogIHJldHVybiBgPGRpdiBjbGFzcz0iZmxleCBqdXN0aWZ5LWJldHdlZW4gZ2FwLTEuNSI+JHtbMSwyLDMsNCw1XS5tYXAoKG4pPT5gCiAgICA8YnV0dG9uIGRhdGEtYWN0aW9uPSJzZXRGb3JtIiBkYXRhLWtleT0iJHtuYW1lfSIgZGF0YS12YWx1ZT0iJHtufSIgY2xhc3M9ImZsZXgtMSBweS0yLjUgcm91bmRlZC1sZyB0ZXh0LXNtIGZvbnQtYm9sZCBib3JkZXIgJHt2PT09bj8iYmctdGVhbC04MDAgdGV4dC13aGl0ZSBib3JkZXItdGVhbC04MDAiOiJiZy13aGl0ZSB0ZXh0LXN0b25lLTUwMCBib3JkZXItc3RvbmUtMjAwIn0iPiR7ZmFEaWdpdHMobil9PC9idXR0b24+CiAgYCkuam9pbigiIil9PC9kaXY+YDsKfQpmdW5jdGlvbiBSYXRpbmdSb3cobGFiZWwsIG5hbWUpIHsgcmV0dXJuIGA8ZGl2PjxwIGNsYXNzPSJ0ZXh0LXNtIHRleHQtc3RvbmUtNzAwIG1iLTIiPiR7ZXNjKGxhYmVsKX08L3A+JHtTY2FsZUlucHV0KG5hbWUpfTwvZGl2PmA7IH0KZnVuY3Rpb24gVG9hc3QodCkgeyBpZighdCkgcmV0dXJuICIiOyBjb25zdCBjbHMgPSB0LnRvbmU9PT0icm9zZSI/ImJnLXJvc2UtMTAwIHRleHQtcm9zZS03MDAiOiJiZy1lbWVyYWxkLTEwMCB0ZXh0LWVtZXJhbGQtNzAwIjsgcmV0dXJuIGA8ZGl2IGNsYXNzPSJtYi00IHAtMyByb3VuZGVkLXhsIHRleHQtc20gZm9udC1zZW1pYm9sZCB0ZXh0LWNlbnRlciAke2Nsc30iPiR7ZXNjKHQubXNnKX08L2Rpdj5gOyB9CmZ1bmN0aW9uIEVycm9yQm94KG0pIHsgaWYoIW0pIHJldHVybiAiIjsgcmV0dXJuIGA8ZGl2IGNsYXNzPSJtYi00IHAtMyByb3VuZGVkLXhsIHRleHQtc20gZm9udC1zZW1pYm9sZCB0ZXh0LWNlbnRlciBiZy1yb3NlLTEwMCB0ZXh0LXJvc2UtNzAwIj4ke2VzYyhtKX08L2Rpdj5gOyB9CmZ1bmN0aW9uIEJhclJvdyhsYWJlbCwgdmFsdWUsIG1heCwgdG9uZT0iYW1iZXIiKSB7CiAgY29uc3QgcGN0ID0gbWF4ID4gMCA/IE1hdGgucm91bmQoKHZhbHVlL21heCkqMTAwKSA6IDA7CiAgY29uc3QgY29sb3JzID0geyBhbWJlcjoiYmctYW1iZXItNTAwIiwgdGVhbDoiYmctdGVhbC03MDAiLCBlbWVyYWxkOiJiZy1lbWVyYWxkLTYwMCIgfTsKICByZXR1cm4gYDxkaXYgY2xhc3M9Im1iLTMiPgogICAgPGRpdiBjbGFzcz0iZmxleCBqdXN0aWZ5LWJldHdlZW4gdGV4dC14cyB0ZXh0LXN0b25lLTYwMCBtYi0xIj48c3Bhbj4ke2VzYyhsYWJlbCl9PC9zcGFuPjxzcGFuIGNsYXNzPSJmb250LWJvbGQiPiR7ZmFEaWdpdHModmFsdWUpfTwvc3Bhbj48L2Rpdj4KICAgIDxkaXYgY2xhc3M9InctZnVsbCBoLTIuNSBiZy1zdG9uZS0xMDAgcm91bmRlZC1mdWxsIG92ZXJmbG93LWhpZGRlbiI+PGRpdiBjbGFzcz0iJHtjb2xvcnNbdG9uZV19IGgtZnVsbCByb3VuZGVkLWZ1bGwiIHN0eWxlPSJ3aWR0aDoke3BjdH0lIj48L2Rpdj48L2Rpdj4KICA8L2Rpdj5gOwp9CmZ1bmN0aW9uIFN0YXRDYXJkKGljb24sIGxhYmVsLCB2YWx1ZSkgewogIHJldHVybiBDYXJkKGA8ZGl2IGNsYXNzPSJwLTQiPjxkaXYgY2xhc3M9InctOSBoLTkgcm91bmRlZC1sZyBmbGV4IGl0ZW1zLWNlbnRlciBqdXN0aWZ5LWNlbnRlciBtYi0yIGJnLXRlYWwtNTAgdGV4dC1sZyI+JHtpY29ufTwvZGl2PgogICAgPHAgY2xhc3M9InRleHQtMnhsIGZvbnQtZXh0cmFib2xkIHRleHQtdGVhbC05NTAiPiR7ZmFEaWdpdHModmFsdWU9PW51bGw/Ii0iOnZhbHVlKX08L3A+PHAgY2xhc3M9InRleHQteHMgdGV4dC1zdG9uZS00MDAiPiR7ZXNjKGxhYmVsKX08L3A+PC9kaXY+YCk7Cn0KCi8qID09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PQogICDYtdmB2K3Zh+KAjNuMINmI2LHZiNivINin2LXZhNuMCiAgID09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PSAqLwpmdW5jdGlvbiBzY3JlZW5MYW5kaW5nKCkgewogIHJldHVybiBgPGRpdiBjbGFzcz0ibWluLWgtc2NyZWVuIGZsZXggZmxleC1jb2wgaXRlbXMtY2VudGVyIGp1c3RpZnktY2VudGVyIHAtNiI+CiAgICA8ZGl2IGNsYXNzPSJ3LWZ1bGwgbWF4LXctc20gZmFkZS1pbiI+CiAgICAgIDxkaXYgY2xhc3M9ImZsZXggZmxleC1jb2wgaXRlbXMtY2VudGVyIG1iLTEwIj4KICAgICAgICA8ZGl2IGNsYXNzPSJ3LTE2IGgtMTYgcm91bmRlZC0yeGwgYmctdGVhbC05MDAgZmxleCBpdGVtcy1jZW50ZXIganVzdGlmeS1jZW50ZXIgbWItNCBzaGFkb3ctbGcgc2hhZG93LXRlYWwtOTAwLzIwIj48c3BhbiBjbGFzcz0idGV4dC0zeGwiPiYjMTI4MTY3Ozwvc3Bhbj48L2Rpdj4KICAgICAgICA8aDEgY2xhc3M9InRleHQtMnhsIGZvbnQtZXh0cmFib2xkIHRleHQtdGVhbC05NTAgdGV4dC1jZW50ZXIiPtmF2LHaqdiyINin2YfYr9inINm+2YTYp9iz2YXYpyDZhtmI24zZhiDZvtmE2KfYs9mF2Kcg2b7ZiNix2Kcg2K/Yp9ix2Yg8L2gxPgogICAgICAgIDxwIGNsYXNzPSJ0ZXh0LXN0b25lLTUwMCB0ZXh0LXNtIG10LTEiPtmG2LjYsdiz2YbYrNuM2Iwg2b7Yp9uM2LQg2LPZhNin2YXYqiDZiCDZhdiv24zYsduM2Kog2YbZiNio2Kog2KfZh9iv2KfaqdmG2YbYr9qv2KfZhjwvcD4KICAgICAgPC9kaXY+CiAgICAgIDxkaXYgY2xhc3M9InNwYWNlLXktMyI+CiAgICAgICAgJHtQcmltYXJ5QnV0dG9uKCLZhdmGINin2YfYr9in2qnZhtmG2K/Zh+KAjNin2YUiLCAiZ29Eb25vckF1dGgiKX0KICAgICAgICAke0dob3N0QnV0dG9uKCLZiNix2YjYryDaqdin2LHaqdmG2KfZhiDZhdix2qnYsiIsICJnb1N0YWZmTG9naW4iKX0KICAgICAgPC9kaXY+CiAgICA8L2Rpdj4KICA8L2Rpdj5gOwp9CgovKiA9PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT0KICAg2YXYs9uM2LEg2KfZh9iv2KfaqdmG2YbYr9mHOiDZiNix2YjYryDYqNinINqp2K8g2b7bjNin2YXaqduMCiAgID09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PSAqLwpmdW5jdGlvbiBzY3JlZW5Eb25vck90cFBob25lKCkgewogIHJldHVybiBgPGRpdiBjbGFzcz0ibWF4LXctc20gbXgtYXV0byBwLTUiPgogICAgJHtUb3BCYXIoItmI2LHZiNivIC8g2KvYqNiq4oCM2YbYp9mFIiwgImdvTGFuZGluZyIpfSR7RXJyb3JCb3goc3RhdGUuZXJyb3JNc2cpfQogICAgJHtDYXJkKGA8ZGl2IGNsYXNzPSJwLTUiPgogICAgICA8cCBjbGFzcz0idGV4dC1zbSB0ZXh0LXN0b25lLTUwMCBtYi00Ij7YtNmF2KfYsdmHINmF2YjYqNin24zZhCDYrtmI2K8g2LHYpyDZiNin2LHYryDaqdmG24zYryDYqtinINqp2K8g2KrYp9uM24zYryDYqNix2KfYqtmI2YYg2KfYsdiz2KfZhCDYqNi02YcuPC9wPgogICAgICA8aW5wdXQgaWQ9InBob25lSW5wdXQiIGlucHV0bW9kZT0ibnVtZXJpYyIgcGxhY2Vob2xkZXI9IjA5eHh4eHh4eHh4IiBjbGFzcz0idy1mdWxsIGJvcmRlciBib3JkZXItc3RvbmUtMjAwIHJvdW5kZWQteGwgcHgtNCBweS0zIHRleHQtbGcgdHJhY2tpbmctd2lkZXIgdGV4dC1jZW50ZXIgbWItNCIgLz4KICAgICAgJHtQcmltYXJ5QnV0dG9uKCLYp9ix2LPYp9mEINqp2K8iLCAicmVxdWVzdE90cCIpfQogICAgPC9kaXY+YCl9CiAgPC9kaXY+YDsKfQoKZnVuY3Rpb24gc2NyZWVuRG9ub3JPdHBDb2RlKCkgewogIHJldHVybiBgPGRpdiBjbGFzcz0ibWF4LXctc20gbXgtYXV0byBwLTUiPgogICAgJHtUb3BCYXIoItqp2K8g2KrYp9uM24zYryIsICJnb0Rvbm9yQXV0aCIpfSR7RXJyb3JCb3goc3RhdGUuZXJyb3JNc2cpfQogICAgJHtzdGF0ZS5mb3JtLmRlbW9Db2RlID8gYDxkaXYgY2xhc3M9Im1iLTQgcC0zIHJvdW5kZWQteGwgdGV4dC1zbSBiZy1hbWJlci0xMDAgdGV4dC1hbWJlci04MDAgdGV4dC1jZW50ZXIiPtqG2YjZhiDYs9ix2YjbjNizINm+24zYp9mF2qkg2YfZhtmI2LIg2YjYtdmEINmG2LTYr9mH2Iwg2qnYryDYqNmH4oCM2LXZiNix2Kog2KLYstmF2KfbjNi024wg2YfZhduM2YbYrNinINmG2LTZiNmGINiv2KfYr9mHINmF24zigIzYtNmHOiA8YiBjbGFzcz0idGV4dC1sZyI+JHtmYURpZ2l0cyhzdGF0ZS5mb3JtLmRlbW9Db2RlKX08L2I+PC9kaXY+YCA6IGA8ZGl2IGNsYXNzPSJtYi00IHAtMyByb3VuZGVkLXhsIHRleHQtc20gYmctdGVhbC01MCB0ZXh0LXRlYWwtODAwIHRleHQtY2VudGVyIj7aqdivINiq2KfbjNuM2K8g2KjYsdin24wgJHtlc2Moc3RhdGUuZm9ybS5waG9uZSl9INm+24zYp9mF2qkg2LTYry48L2Rpdj5gfQogICAgJHtDYXJkKGA8ZGl2IGNsYXNzPSJwLTUiPgogICAgICA8aW5wdXQgaWQ9Im90cElucHV0IiBpbnB1dG1vZGU9Im51bWVyaWMiIHBsYWNlaG9sZGVyPSLaqdivINu2INix2YLZhduMIiBjbGFzcz0idy1mdWxsIGJvcmRlciBib3JkZXItc3RvbmUtMjAwIHJvdW5kZWQteGwgcHgtNCBweS0zIHRleHQtbGcgdHJhY2tpbmctd2lkZXN0IHRleHQtY2VudGVyIG1iLTQiIC8+CiAgICAgICR7UHJpbWFyeUJ1dHRvbigi2KrYp9uM24zYryIsICJ2ZXJpZnlPdHAiKX0KICAgIDwvZGl2PmApfQogIDwvZGl2PmA7Cn0KCmZ1bmN0aW9uIHNjcmVlbkRvbm9yUmVnaXN0ZXIoKSB7CiAgcmV0dXJuIGA8ZGl2IGNsYXNzPSJtYXgtdy1zbSBteC1hdXRvIHAtNSI+CiAgICAke1RvcEJhcigi2KvYqNiq4oCM2YbYp9mFIiwgbnVsbCl9JHtFcnJvckJveChzdGF0ZS5lcnJvck1zZyl9CiAgICAke0NhcmQoYDxkaXYgY2xhc3M9InAtNSBzcGFjZS15LTMiPgogICAgICA8cCBjbGFzcz0idGV4dC1zbSB0ZXh0LXN0b25lLTUwMCI+2KfZiNmE24zZhiDYrdi22YjYsdiq2YjZhtmHISDZhNi32YHYp9mLINin2LfZhNin2LnYp9iqINiy24zYsSDYsdmIINiq2qnZhduM2YQg2qnZhtuM2K8uPC9wPgogICAgICA8ZGl2PjxsYWJlbCBjbGFzcz0idGV4dC14cyBmb250LXNlbWlib2xkIHRleHQtc3RvbmUtNTAwIj7Zhtin2YU8L2xhYmVsPjxpbnB1dCBpZD0iZmlyc3ROYW1lSW5wdXQiIGNsYXNzPSJ3LWZ1bGwgYm9yZGVyIGJvcmRlci1zdG9uZS0yMDAgcm91bmRlZC14bCBweC00IHB5LTMgbXQtMSIgLz48L2Rpdj4KICAgICAgPGRpdj48bGFiZWwgY2xhc3M9InRleHQteHMgZm9udC1zZW1pYm9sZCB0ZXh0LXN0b25lLTUwMCI+2YbYp9mFINiu2KfZhtmI2KfYr9qv24w8L2xhYmVsPjxpbnB1dCBpZD0ibGFzdE5hbWVJbnB1dCIgY2xhc3M9InctZnVsbCBib3JkZXIgYm9yZGVyLXN0b25lLTIwMCByb3VuZGVkLXhsIHB4LTQgcHktMyBtdC0xIiAvPjwvZGl2PgogICAgICA8ZGl2PjxsYWJlbCBjbGFzcz0idGV4dC14cyBmb250LXNlbWlib2xkIHRleHQtc3RvbmUtNTAwIj7Ys9mGPC9sYWJlbD48aW5wdXQgaWQ9ImFnZUlucHV0IiB0eXBlPSJudW1iZXIiIG1pbj0iMTciIG1heD0iNzUiIGNsYXNzPSJ3LWZ1bGwgYm9yZGVyIGJvcmRlci1zdG9uZS0yMDAgcm91bmRlZC14bCBweC00IHB5LTMgbXQtMSIgLz48L2Rpdj4KICAgICAgJHtQcmltYXJ5QnV0dG9uKCLYqtqp2YXbjNmEINir2KjYquKAjNmG2KfZhSIsICJzdWJtaXRSZWdpc3RlciIpfQogICAgPC9kaXY+YCl9CiAgPC9kaXY+YDsKfQoKLyogPT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09CiAgINmG2LjYsdiz2YbYrNuMINin2YjZhNuM2YYg2YXYsdin2KzYudmHICjZgdmC2Lcg24zaqeKAjNio2KfYsSkKICAgPT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09ICovCmZ1bmN0aW9uIHNjcmVlbkRvbm9yU3VydmV5KCkgewogIGNvbnN0IGYgPSBzdGF0ZS5mb3JtOwogIGNvbnN0IGZpbGxlZCA9IFNVUlZFWV9DQVRFR09SSUVTLmV2ZXJ5KChba2V5XSkgPT4gZltrZXldKSAmJiBmLnJlZmVycmFsU291cmNlOwogIHJldHVybiBgPGRpdiBjbGFzcz0ibWF4LXctc20gbXgtYXV0byBwLTUgcGItMTAiPgogICAgJHtUb3BCYXIoItmG2LjYsdiz2YbYrNuMINin2YjZhNuM2YYg2YXYsdin2KzYudmHIil9JHtFcnJvckJveChzdGF0ZS5lcnJvck1zZyl9CiAgICAke0NhcmQoYDxkaXYgY2xhc3M9InAtNSBzcGFjZS15LTUiPgogICAgICA8cCBjbGFzcz0idGV4dC14cyB0ZXh0LXN0b25lLTQwMCI+2KfbjNmGINmG2LjYsdiz2YbYrNuMINmB2YLYtyDbjNqp4oCM2KjYp9ix2Iwg2KjYsdin24wg2KfZiNmE24zZhiDZhdix2KfYrNi52YfigIzbjCDYtNmF2Kcg2KraqdmF24zZhCDZhduM4oCM2LTZhy48L3A+CiAgICAgICR7U1VSVkVZX0NBVEVHT1JJRVMubWFwKChba2V5LGxhYmVsXSkgPT4gUmF0aW5nUm93KGxhYmVsLCBrZXkpKS5qb2luKCIiKX0KICAgICAgPGRpdj48cCBjbGFzcz0idGV4dC1zbSBmb250LXNlbWlib2xkIHRleHQtdGVhbC05NTAgbWItMiI+2obYt9mI2LEg2KjYpyDZhdix2qnYsiDYoti02YbYpyDYtNiv24zYr9ifPC9wPgogICAgICAgIDxkaXYgY2xhc3M9ImdyaWQgZ3JpZC1jb2xzLTIgZ2FwLTIiPiR7UkVGRVJSQUxfT1BUSU9OUy5tYXAoKG8pID0+IGAKICAgICAgICAgIDxidXR0b24gZGF0YS1hY3Rpb249InNldEZvcm0iIGRhdGEta2V5PSJyZWZlcnJhbFNvdXJjZSIgZGF0YS12YWx1ZT0iJHtlc2Mobyl9IiBjbGFzcz0icHktMi41IHJvdW5kZWQtbGcgdGV4dC14cyBib3JkZXIgJHtmLnJlZmVycmFsU291cmNlPT09bz8iYmctdGVhbC04MDAgdGV4dC13aGl0ZSBib3JkZXItdGVhbC04MDAiOiJiZy13aGl0ZSBib3JkZXItc3RvbmUtMjAwIHRleHQtc3RvbmUtNjAwIn0iPiR7ZXNjKG8pfTwvYnV0dG9uPgogICAgICAgIGApLmpvaW4oIiIpfTwvZGl2PgogICAgICA8L2Rpdj4KICAgICAgPGRpdj48cCBjbGFzcz0idGV4dC1zbSBmb250LXNlbWlib2xkIHRleHQtdGVhbC05NTAgbWItMiI+2b7bjNi02YbZh9in2K8g24zYpyDYp9mG2KrZgtin2K8gKNin2K7YqtuM2KfYsduMKTwvcD4KICAgICAgICA8dGV4dGFyZWEgaWQ9ImZyZWVUZXh0SW5wdXQiIHJvd3M9IjMiIGNsYXNzPSJ3LWZ1bGwgYm9yZGVyIGJvcmRlci1zdG9uZS0yMDAgcm91bmRlZC14bCBweC00IHB5LTMiPjwvdGV4dGFyZWE+CiAgICAgIDwvZGl2PgogICAgICAke1ByaW1hcnlCdXR0b24oItir2KjYqiDZhti42LHYs9mG2KzbjCIsICJzdWJtaXRTdXJ2ZXkiLCB7IGRpc2FibGVkOiAhZmlsbGVkIH0pfQogICAgPC9kaXY+YCl9CiAgPC9kaXY+YDsKfQoKZnVuY3Rpb24gc2NyZWVuRG9ub3JUZXN0UGVuZGluZygpIHsKICByZXR1cm4gYDxkaXYgY2xhc3M9Im1heC13LXNtIG14LWF1dG8gcC01Ij4KICAgICR7VG9wQmFyKCLYr9ixINin2YbYqti42KfYsSDZhtiq24zYrNmHIiwgImRvbm9yTG9nb3V0Iil9CiAgICAke0NhcmQoYDxkaXYgY2xhc3M9InAtNiB0ZXh0LWNlbnRlciI+CiAgICAgIDxkaXYgY2xhc3M9InctMTQgaC0xNCByb3VuZGVkLWZ1bGwgYmctYW1iZXItMTAwIGZsZXggaXRlbXMtY2VudGVyIGp1c3RpZnktY2VudGVyIG14LWF1dG8gbWItNCI+PHNwYW4gY2xhc3M9InRleHQtMnhsIj4mIzkyMDM7PC9zcGFuPjwvZGl2PgogICAgICA8cCBjbGFzcz0idGV4dC1zbSB0ZXh0LXN0b25lLTYwMCBsZWFkaW5nLTciPtin2LIg2KvYqNiqINmG2LjYsSDYtNmF2Kcg2LPZvtin2LPar9iy2KfYsduM2YUuINmG2KrYp9uM2Kwg2KLYstmF2KfbjNi04oCM2YfYp9uMINi02YXYpyDZvtizINin2LIg2K3Yr9mI2K8g27cg2KrYpyDbsduwINix2YjYsiDYotmF2KfYr9mHINiu2YjYp9mH2K8g2LTYry4g2b7YsyDYp9iyINiq2KPbjNuM2K/YjCDZvtmG2YQg2LTZhdinINmB2LnYp9mEINi02K/ZhyDZiCDYp9mF2qnYp9mGINiq2LnbjNuM2YYg2LLZhdin2YYg2YXYsdin2KzYudmHINio2LHYp9uMINin2YjZhNuM2YYg2KfZh9iv2Kcg2YHYsdin2YfZhSDZhduM4oCM2LTZiNivLiDZhtiq24zYrNmHINin2LIg2LfYsduM2YIg2b7bjNin2YXaqSDZhtuM2LIg2KfYt9mE2KfYueKAjNix2LPYp9mG24wg2K7ZiNin2YfYryDYtNivLjwvcD4KICAgIDwvZGl2PmApfQogICAgJHtOb3RpZmljYXRpb25zTGlzdCgpfQogIDwvZGl2PmA7Cn0KCmZ1bmN0aW9uIE5vdGlmaWNhdGlvbnNMaXN0KCkgewogIGlmICghc3RhdGUuZG9ub3JOb3RpZmljYXRpb25zIHx8IHN0YXRlLmRvbm9yTm90aWZpY2F0aW9ucy5sZW5ndGggPT09IDApIHJldHVybiAiIjsKICBjb25zdCBsYXRlc3QgPSBzdGF0ZS5kb25vck5vdGlmaWNhdGlvbnNbMF07CiAgcmV0dXJuIGA8ZGl2IGNsYXNzPSJtdC00Ij4ke0NhcmQoYDxkaXYgY2xhc3M9InAtNCBiZy10ZWFsLTUwIGJvcmRlci10ZWFsLTIwMCI+CiAgICA8ZGl2IGNsYXNzPSJmbGV4IGl0ZW1zLWNlbnRlciBnYXAtMiBtYi0yIHRleHQtdGVhbC04MDAgZm9udC1ib2xkIHRleHQtc20iPiYjMTI4MTcyOyDYotiu2LHbjNmGINm+24zYp9mFPC9kaXY+CiAgICA8cCBjbGFzcz0idGV4dC1zbSB0ZXh0LXN0b25lLTcwMCI+JHtlc2MobGF0ZXN0LnRleHQpfTwvcD4KICAgIDxwIGNsYXNzPSJ0ZXh0LXhzIHRleHQtc3RvbmUtNDAwIG10LTIiPiR7Zm10RGF0ZVNob3J0KGxhdGVzdC5jcmVhdGVkQXQpfTwvcD4KICA8L2Rpdj5gKX08L2Rpdj5gOwp9CgovKiA9PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT0KICAg2K7Yp9mG2YfigIzbjCDYp9mH2K/Yp9qp2YbZhtiv2YcKICAgPT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09ICovCmZ1bmN0aW9uIHNjcmVlbkRvbm9ySG9tZSgpIHsKICBjb25zdCBkID0gc3RhdGUuZG9ub3I7CiAgaWYgKCFkKSByZXR1cm4gYDxkaXYgY2xhc3M9InAtMTAgdGV4dC1jZW50ZXIgdGV4dC1zdG9uZS00MDAiPtiv2LEg2K3Yp9mEINio2KfYsdqv2LDYp9ix24wuLi48L2Rpdj5gOwogIGNvbnN0IGFwcHQgPSBkLmN1cnJlbnRBcHBvaW50bWVudDsKICByZXR1cm4gYDxkaXYgY2xhc3M9Im1heC13LXNtIG14LWF1dG8gcC01IHBiLTEwIj4KICAgIDxkaXYgY2xhc3M9ImZsZXggaXRlbXMtY2VudGVyIGp1c3RpZnktYmV0d2VlbiBtYi01Ij4KICAgICAgPGJ1dHRvbiBkYXRhLWFjdGlvbj0iZG9ub3JMb2dvdXQiIGNsYXNzPSJwLTIgLW1sLTIgdGV4dC1zdG9uZS00MDAgdGV4dC1sZyI+JiM4Njc0OzwvYnV0dG9uPgogICAgICA8ZGl2IGNsYXNzPSJ0ZXh0LWNlbnRlciI+PHAgY2xhc3M9InRleHQteHMgdGV4dC1zdG9uZS00MDAiPtiu2YjYtCDYp9mI2YXYr9uMPC9wPjxwIGNsYXNzPSJmb250LWJvbGQgdGV4dC10ZWFsLTk1MCI+JHtlc2MoZC5maXJzdE5hbWUpfSAke2VzYyhkLmxhc3ROYW1lKX08L3A+PC9kaXY+CiAgICAgIDxkaXYgY2xhc3M9InctOSI+PC9kaXY+CiAgICA8L2Rpdj4KICAgICR7VG9hc3Qoc3RhdGUudG9hc3QpfSR7RXJyb3JCb3goc3RhdGUuZXJyb3JNc2cpfQoKICAgICR7Q2FyZChgPGRpdiBjbGFzcz0icC00IGZsZXggaXRlbXMtY2VudGVyIGdhcC0zIj4KICAgICAgPHNwYW4gY2xhc3M9InRleHQtMnhsIj4mIzg1MDU7JiM2NTAzOTs8L3NwYW4+CiAgICAgIDxkaXY+PHAgY2xhc3M9ImZvbnQtYm9sZCB0ZXh0LXRlYWwtOTUwIj4ke1NUQVRVU19MQUJFTFNbZC5zdGF0dXNdIHx8IGQuc3RhdHVzfTwvcD4KICAgICAgPHAgY2xhc3M9InRleHQteHMgdGV4dC1zdG9uZS01MDAiPiR7ZC5hcHBvaW50bWVudHMuZmlsdGVyKGE9PmEuZG9uYXRlZD09PXRydWUpLmxlbmd0aCA/IGDYqtinINin2YTYp9mGICR7ZmFEaWdpdHMoZC5hcHBvaW50bWVudHMuZmlsdGVyKGE9PmEuZG9uYXRlZD09PXRydWUpLmxlbmd0aCl9INio2KfYsSDYp9mH2K/YpyDaqdix2K/bjNivYCA6ICLZh9mG2YjYsiDYp9mH2K/Yp9uM24wg2KvYqNiqINmG2LTYr9mHIn08L3A+PC9kaXY+CiAgICA8L2Rpdj5gLCAibWItNCIpfQoKICAgICR7Tm90aWZpY2F0aW9uc0xpc3QoKX0KCiAgICAke2FwcHQgPyBBcHBvaW50bWVudENhcmQoYXBwdCkgOiAoCiAgICAgIGQuZWxpZ2libGVGb3JCb29raW5nID8gQ2FyZChgPGRpdiBjbGFzcz0icC00Ij4KICAgICAgICA8cCBjbGFzcz0iZm9udC1ib2xkIHRleHQtdGVhbC05NTAgbWItMyI+2YXbjOKAjNiq2YjZhtuM2K8g2YbZiNio2Kog2KfZh9iv2Kcg2LHYstix2Ygg2qnZhtuM2K88L3A+CiAgICAgICAgJHtQcmltYXJ5QnV0dG9uKCLYsdiy2LHZiCDZhtmI2KjYqiIsICJnb0Jvb2tBcHBvaW50bWVudCIpfQogICAgICA8L2Rpdj5gLCAibWItNCBiZy1lbWVyYWxkLTUwIGJvcmRlci1lbWVyYWxkLTIwMCIpIDoKICAgICAgZC5uZXh0RWxpZ2libGVEYXRlID8gQ2FyZChgPGRpdiBjbGFzcz0icC00Ij48cCBjbGFzcz0idGV4dC1zbSB0ZXh0LXN0b25lLTYwMCI+2YbZiNio2Kog2KjYudiv24wg2KfYsiDYqtin2LHbjNiuIDxiPiR7Zm10RGF0ZShkLm5leHRFbGlnaWJsZURhdGUpfTwvYj4g2YLYp9io2YQg2LHYstix2YjZhy48L3A+PC9kaXY+YCwgIm1iLTQiKSA6ICIiCiAgICApfQoKICAgICR7KGQucGVuZGluZ0ZvbGxvd1VwcyAmJiBkLnBlbmRpbmdGb2xsb3dVcHMubGVuZ3RoID4gMCkgPyBDYXJkKGA8ZGl2IGNsYXNzPSJwLTQiPgogICAgICA8ZGl2IGNsYXNzPSJmbGV4IGl0ZW1zLWNlbnRlciBnYXAtMyBtYi0zIj48c3BhbiBjbGFzcz0idGV4dC0yeGwiPiYjMTI4MjAyOzwvc3Bhbj4KICAgICAgICA8ZGl2PjxwIGNsYXNzPSJmb250LWJvbGQgdGV4dC10ZWFsLTk1MCI+2b7bjNqv24zYsduMINm+2LMg2KfYsiDYp9mH2K/YpzwvcD48cCBjbGFzcz0idGV4dC14cyB0ZXh0LXN0b25lLTUwMCI+2YTYt9mB2KfZiyDZiNi22LnbjNiqINiz2YTYp9mF2KrYqtmI2YYg2LHZiCDYq9io2Kog2qnZhtuM2K8gKNix2YjYsiAke2ZhRGlnaXRzKGQucGVuZGluZ0ZvbGxvd1Vwc1swXS5kYXlJbmRleCl9KTwvcD48L2Rpdj4KICAgICAgPC9kaXY+CiAgICAgICR7UHJpbWFyeUJ1dHRvbigi2KraqdmF24zZhCDZgdix2YUg2b7bjNqv24zYsduMIiwgIm9wZW5Gb2xsb3dVcCIsIHsgZGF0YTogeyBhcHB0OiBkLnBlbmRpbmdGb2xsb3dVcHNbMF0uYXBwb2ludG1lbnRJZCwgZGF5OiBkLnBlbmRpbmdGb2xsb3dVcHNbMF0uZGF5SW5kZXggfSB9KX0KICAgIDwvZGl2PmAsICJtYi00IGJnLWFtYmVyLTUwIGJvcmRlci1hbWJlci0yMDAiKSA6ICIifQoKICAgIDxwIGNsYXNzPSJ0ZXh0LXhzIGZvbnQtYm9sZCB0ZXh0LXN0b25lLTQwMCBtYi0yIj7Yqtin2LHbjNiu2obZh+KAjNuMINmG2YjYqNiq4oCM2YfYpzwvcD4KICAgIDxkaXYgY2xhc3M9InNwYWNlLXktMiI+CiAgICAgICR7ZC5hcHBvaW50bWVudHMubGVuZ3RoPT09MCA/IGA8cCBjbGFzcz0idGV4dC1zbSB0ZXh0LXN0b25lLTQwMCB0ZXh0LWNlbnRlciBweS02Ij7Zh9mG2YjYsiDZhtmI2KjYqtuMINir2KjYqiDZhti02K/ZhzwvcD5gIDogWy4uLmQuYXBwb2ludG1lbnRzXS5zb3J0KChhLGIpPT5uZXcgRGF0ZShiLmNyZWF0ZWRBdCktbmV3IERhdGUoYS5jcmVhdGVkQXQpKS5tYXAoKGEpID0+IGAKICAgICAgICAke0NhcmQoYDxkaXYgY2xhc3M9InAtMy41IGZsZXggaXRlbXMtY2VudGVyIGp1c3RpZnktYmV0d2VlbiI+CiAgICAgICAgICA8ZGl2PjxwIGNsYXNzPSJ0ZXh0LXNtIGZvbnQtc2VtaWJvbGQgdGV4dC10ZWFsLTk1MCI+JHtmbXREYXRlVGltZShhLmNvbmZpcm1lZERhdGV8fGEucmVxdWVzdGVkRGF0ZSl9PC9wPgogICAgICAgICAgPHAgY2xhc3M9InRleHQteHMgdGV4dC1zdG9uZS00MDAiPiR7YS5zdGF0dXM9PT0iY2FuY2VsbGVkIj8i2YTYutmI2LTYr9mHIjphLmRvbmF0ZWQ9PT10cnVlPyLYp9mH2K/YpyDYp9mG2KzYp9mFINi02K8iOmEuZG9uYXRlZD09PWZhbHNlPyLYp9mH2K/YpyDYp9mG2KzYp9mFINmG2LTYryI6YS5zdGF0dXM9PT0iY29uZmlybWVkIj8i2KrYp9uM24zYr9i02K/ZhyI6YS5zdGF0dXM9PT0icmVxdWVzdGVkIj8i2K/YsSDYp9mG2KrYuNin2LEg2KrYp9uM24zYryI6YS5zdGF0dXN9PC9wPjwvZGl2PgogICAgICAgIDwvZGl2PmApfQogICAgICBgKS5qb2luKCIiKX0KICAgIDwvZGl2PgogIDwvZGl2PmA7Cn0KCmZ1bmN0aW9uIEFwcG9pbnRtZW50Q2FyZChhcHB0KSB7CiAgaWYgKGFwcHQuc3RhdHVzID09PSAicmVxdWVzdGVkIikgewogICAgcmV0dXJuIENhcmQoYDxkaXYgY2xhc3M9InAtNCI+PHAgY2xhc3M9ImZvbnQtYm9sZCB0ZXh0LXRlYWwtOTUwIG1iLTEiPtiv2LHYrtmI2KfYs9iqINmG2YjYqNiqINi02YXYpyDYq9io2Kog2LTYrzwvcD4KICAgICAgPHAgY2xhc3M9InRleHQteHMgdGV4dC1zdG9uZS01MDAgbWItMyI+2LLZhdin2YYg2K/Ysdiu2YjYp9iz2KrbjDogJHtmbXREYXRlVGltZShhcHB0LnJlcXVlc3RlZERhdGUpfSDigJQg2YXZhtiq2LjYsSDYqtin24zbjNivINmF2K/bjNixINio2KfYtNuM2K8uPC9wPgogICAgICAke1NtYWxsQnV0dG9uKCLZhNi62Ygg2K/Ysdiu2YjYp9iz2KoiLCAiY2FuY2VsQXBwb2ludG1lbnQiLCB7IGRhdGE6IHsgaWQ6IGFwcHQuaWQgfSwgdG9uZTogInJvc2UiIH0pfQogICAgPC9kaXY+YCwgIm1iLTQgYmctYW1iZXItNTAgYm9yZGVyLWFtYmVyLTIwMCIpOwogIH0KICBpZiAoYXBwdC5zdGF0dXMgPT09ICJyZXNjaGVkdWxlZF9ieV9hZG1pbiIpIHsKICAgIHJldHVybiBDYXJkKGA8ZGl2IGNsYXNzPSJwLTQiPjxwIGNsYXNzPSJmb250LWJvbGQgdGV4dC10ZWFsLTk1MCBtYi0xIj7YstmF2KfZhiDZvtuM2LTZhtmH2KfYr9uMINis2K/bjNivPC9wPgogICAgICA8cCBjbGFzcz0idGV4dC1zbSB0ZXh0LXN0b25lLTYwMCBtYi0zIj4ke2ZtdERhdGVUaW1lKGFwcHQuY29uZmlybWVkRGF0ZSl9JHthcHB0LmFkbWluTm90ZSA/ICIg4oCUICIgKyBlc2MoYXBwdC5hZG1pbk5vdGUpIDogIiJ9PC9wPgogICAgICA8ZGl2IGNsYXNzPSJncmlkIGdyaWQtY29scy0yIGdhcC0yIj4KICAgICAgICAke1NtYWxsQnV0dG9uKCLZgtio2YjZhCDYr9in2LHZhSIsICJhY2NlcHRSZXNjaGVkdWxlIiwgeyBkYXRhOiB7IGlkOiBhcHB0LmlkIH0sIHRvbmU6ICJlbWVyYWxkIiB9KX0KICAgICAgICAke1NtYWxsQnV0dG9uKCLZhNi62Ygg2YbZiNio2KoiLCAiY2FuY2VsQXBwb2ludG1lbnQiLCB7IGRhdGE6IHsgaWQ6IGFwcHQuaWQgfSwgdG9uZTogInJvc2UiIH0pfQogICAgICA8L2Rpdj4KICAgIDwvZGl2PmAsICJtYi00IGJnLWFtYmVyLTUwIGJvcmRlci1hbWJlci0yMDAiKTsKICB9CiAgcmV0dXJuIENhcmQoYDxkaXYgY2xhc3M9InAtNCI+PHAgY2xhc3M9ImZvbnQtYm9sZCB0ZXh0LXRlYWwtOTUwIG1iLTEiPtmG2YjYqNiqINi02YXYpyDYqtin24zbjNivINi02K/ZhzwvcD4KICAgIDxwIGNsYXNzPSJ0ZXh0LXNtIHRleHQtc3RvbmUtNjAwIG1iLTMiPiR7Zm10RGF0ZVRpbWUoYXBwdC5jb25maXJtZWREYXRlKX08L3A+CiAgICAke1NtYWxsQnV0dG9uKCLZhNi62Ygg2YbZiNio2KoiLCAiY2FuY2VsQXBwb2ludG1lbnQiLCB7IGRhdGE6IHsgaWQ6IGFwcHQuaWQgfSwgdG9uZTogInJvc2UiIH0pfQogIDwvZGl2PmAsICJtYi00IGJnLWVtZXJhbGQtNTAgYm9yZGVyLWVtZXJhbGQtMjAwIik7Cn0KCmZ1bmN0aW9uIHNjcmVlbkRvbm9yQm9vaygpIHsKICBjb25zdCBkYXRlID0gc3RhdGUuZm9ybS5ib29rRGF0ZSB8fCB0b2RheUlTT0RhdGUoKTsKICBjb25zdCBzbG90cyA9IHN0YXRlLmZvcm0uc2xvdHMgfHwgW107CiAgY29uc3QgbW9kZSA9IHN0YXRlLmZvcm0uYXBwb2ludG1lbnRNb2RlIHx8ICJhdXRvIjsKICByZXR1cm4gYDxkaXYgY2xhc3M9Im1heC13LXNtIG14LWF1dG8gcC01Ij4KICAgICR7VG9wQmFyKCLYsdiy2LHZiCDZhtmI2KjYqiDYp9mH2K/YpyIsICJiYWNrVG9Eb25vckhvbWUiKX0ke0Vycm9yQm94KHN0YXRlLmVycm9yTXNnKX0KICAgICR7Q2FyZChgPGRpdiBjbGFzcz0icC01Ij4KICAgICAgPGxhYmVsIGNsYXNzPSJ0ZXh0LXhzIGZvbnQtc2VtaWJvbGQgdGV4dC1zdG9uZS01MDAiPtiq2KfYsduM2K4g2YXZiNix2K8g2YbYuNixPC9sYWJlbD4KICAgICAgPGlucHV0IGlkPSJib29rRGF0ZUlucHV0IiB0eXBlPSJkYXRlIiB2YWx1ZT0iJHtkYXRlfSIgY2xhc3M9InctZnVsbCBib3JkZXIgYm9yZGVyLXN0b25lLTIwMCByb3VuZGVkLXhsIHB4LTQgcHktMyBtdC0xIG1iLTMiIC8+CiAgICAgICR7bW9kZSA9PT0gImF1dG8iID8gYAogICAgICAgICR7U21hbGxCdXR0b24oItmG2YXYp9uM2LQg2LPYp9i52KrigIzZh9in24wg2K7Yp9mE24wiLCAibG9hZFNsb3RzIiwgeyB0b25lOiAic3RvbmUiIH0pfQogICAgICAgIDxkaXYgY2xhc3M9ImdyaWQgZ3JpZC1jb2xzLTMgZ2FwLTIgbXQtMyI+CiAgICAgICAgICAke3Nsb3RzLm1hcCgocykgPT4gYDxidXR0b24gZGF0YS1hY3Rpb249InBpY2tTbG90IiBkYXRhLXRpbWU9IiR7cy50aW1lfSIgJHshcy5hdmFpbGFibGU/ImRpc2FibGVkIjoiIn0KICAgICAgICAgICAgY2xhc3M9InB5LTIuNSByb3VuZGVkLWxnIHRleHQtc20gYm9yZGVyICR7c3RhdGUuZm9ybS5waWNrZWRUaW1lPT09cy50aW1lPyJiZy10ZWFsLTgwMCB0ZXh0LXdoaXRlIGJvcmRlci10ZWFsLTgwMCI6ImJnLXdoaXRlIGJvcmRlci1zdG9uZS0yMDAgdGV4dC1zdG9uZS02MDAifSBkaXNhYmxlZDpvcGFjaXR5LTMwIj4ke3MudGltZX08L2J1dHRvbj5gKS5qb2luKCIiKX0KICAgICAgICA8L2Rpdj4KICAgICAgICA8ZGl2IGNsYXNzPSJtdC00Ij4ke1ByaW1hcnlCdXR0b24oItir2KjYqiDZhtmI2KjYqiIsICJzdWJtaXRCb29raW5nIiwgeyBkaXNhYmxlZDogIXN0YXRlLmZvcm0ucGlja2VkVGltZSB9KX08L2Rpdj4KICAgICAgYCA6IGAKICAgICAgICA8bGFiZWwgY2xhc3M9InRleHQteHMgZm9udC1zZW1pYm9sZCB0ZXh0LXN0b25lLTUwMCI+2LPYp9i52Kog2b7bjNi02YbZh9in2K/bjDwvbGFiZWw+CiAgICAgICAgPGlucHV0IGlkPSJib29rVGltZUlucHV0IiB0eXBlPSJ0aW1lIiBjbGFzcz0idy1mdWxsIGJvcmRlciBib3JkZXItc3RvbmUtMjAwIHJvdW5kZWQteGwgcHgtNCBweS0zIG10LTEgbWItMyIgLz4KICAgICAgICA8bGFiZWwgY2xhc3M9InRleHQteHMgZm9udC1zZW1pYm9sZCB0ZXh0LXN0b25lLTUwMCI+2KrZiNi224zYrSAo2KfYrtiq24zYp9ix24wpPC9sYWJlbD4KICAgICAgICA8dGV4dGFyZWEgaWQ9ImJvb2tOb3RlSW5wdXQiIHJvd3M9IjIiIGNsYXNzPSJ3LWZ1bGwgYm9yZGVyIGJvcmRlci1zdG9uZS0yMDAgcm91bmRlZC14bCBweC00IHB5LTMgbXQtMSBtYi0zIj48L3RleHRhcmVhPgogICAgICAgIDxkaXYgY2xhc3M9Im10LTIiPiR7UHJpbWFyeUJ1dHRvbigi2KvYqNiqINiv2LHYrtmI2KfYs9iqINmG2YjYqNiqIiwgInN1Ym1pdEJvb2tpbmciKX08L2Rpdj4KICAgICAgYH0KICAgIDwvZGl2PmApfQogIDwvZGl2PmA7Cn0KCmZ1bmN0aW9uIHNjcmVlbkRvbm9yRm9sbG93VXAoKSB7CiAgY29uc3QgZiA9IHN0YXRlLmZvcm07CiAgY29uc3QgY29tcGxldGUgPSBmLmdlbmVyYWxDb25kaXRpb24gJiYgZi5kaXp6aW5lc3MgIT09IHVuZGVmaW5lZCAmJiBmLmluamVjdGlvblNpdGVJc3N1ZSAhPT0gdW5kZWZpbmVkICYmIGYuc2F0aXNmaWVkICE9PSB1bmRlZmluZWQgJiYgZi5yZWFkeUZvck5leHQgIT09IHVuZGVmaW5lZDsKICByZXR1cm4gYDxkaXYgY2xhc3M9Im1heC13LXNtIG14LWF1dG8gcC01Ij4KICAgICR7VG9wQmFyKCLZvtuM2q/bjNix24wg2b7YsyDYp9iyINin2YfYr9inIil9JHtFcnJvckJveChzdGF0ZS5lcnJvck1zZyl9CiAgICAke0NhcmQoYDxkaXYgY2xhc3M9InAtNSBzcGFjZS15LTUiPgogICAgICA8ZGl2PjxwIGNsYXNzPSJ0ZXh0LXNtIGZvbnQtc2VtaWJvbGQgdGV4dC10ZWFsLTk1MCBtYi0yIj7ZiNi22LnbjNiqINi52YXZiNmF24wg2LTZhdinINqG2q/ZiNmG2Ycg2KfYs9iq2J88L3A+CiAgICAgICAgPGRpdiBjbGFzcz0iZ3JpZCBncmlkLWNvbHMtMyBnYXAtMiI+JHtbItiu2YjYqCIsItmF2KrZiNiz2LciLCLYtti524zZgSJdLm1hcCgobyk9PmAKICAgICAgICAgIDxidXR0b24gZGF0YS1hY3Rpb249InNldEZvcm0iIGRhdGEta2V5PSJnZW5lcmFsQ29uZGl0aW9uIiBkYXRhLXZhbHVlPSIke299IiBjbGFzcz0icHktMyByb3VuZGVkLWxnIHRleHQtc20gYm9yZGVyICR7Zi5nZW5lcmFsQ29uZGl0aW9uPT09bz8iYmctdGVhbC04MDAgdGV4dC13aGl0ZSBib3JkZXItdGVhbC04MDAiOiJiZy13aGl0ZSBib3JkZXItc3RvbmUtMjAwIHRleHQtc3RvbmUtNjAwIn0iPiR7b308L2J1dHRvbj4KICAgICAgICBgKS5qb2luKCIiKX08L2Rpdj4KICAgICAgPC9kaXY+CiAgICAgICR7WWVzTm9Sb3coItii24zYpyDYp9it2LPYp9izINiz2LHar9uM2KzZhyDYr9in2LTYqtmH4oCM2KfbjNiv2J8iLCAiZGl6emluZXNzIil9CiAgICAgICR7WWVzTm9Sb3coItii24zYpyDZhdit2YQg2KrYstix24zZgiDZhdi02qnZhNuMINiv2KfYsdiv2J8iLCAiaW5qZWN0aW9uU2l0ZUlzc3VlIil9CiAgICAgICR7WWVzTm9Sb3coItii24zYpyDYp9iyINix2YjZhtivINin2YfYr9inINix2LbYp9uM2Kog2K/Yp9i02KrbjNiv2J8iLCAic2F0aXNmaWVkIil9CiAgICAgICR7WWVzTm9Sb3coItii24zYpyDYqNix2KfbjCDZhdix2KfYrNi52YfigIzbjCDYqNi52K/bjCDYotmF2KfYr9mH4oCM2KfbjNiv2J8iLCAicmVhZHlGb3JOZXh0Iil9CiAgICAgIDxkaXY+PGxhYmVsIGNsYXNzPSJmbGV4IGl0ZW1zLWNlbnRlciBnYXAtMiB0ZXh0LXNtIHRleHQtc3RvbmUtNjAwIj4KICAgICAgICA8aW5wdXQgdHlwZT0iY2hlY2tib3giIGRhdGEtYWN0aW9uPSJ0b2dnbGVDYWxsYmFjayIgJHtmLmNhbGxiYWNrUmVxdWVzdGVkPyJjaGVja2VkIjoiIn0gLz4g2YXbjOKAjNiu2YjYp9mFINio2KfZh9in2YUg2KrZhdin2LMg2Kjar9uM2LHbjNivCiAgICAgIDwvbGFiZWw+PC9kaXY+CiAgICAgIDxkaXY+PHAgY2xhc3M9InRleHQtc20gZm9udC1zZW1pYm9sZCB0ZXh0LXRlYWwtOTUwIG1iLTIiPtiq2YjYttuM2K0g2KraqdmF24zZhNuMICjYp9iu2KrbjNin2LHbjCk8L3A+CiAgICAgICAgPHRleHRhcmVhIGlkPSJmb2xsb3d1cE5vdGVzIiByb3dzPSIyIiBjbGFzcz0idy1mdWxsIGJvcmRlciBib3JkZXItc3RvbmUtMjAwIHJvdW5kZWQteGwgcHgtNCBweS0zIj48L3RleHRhcmVhPgogICAgICA8L2Rpdj4KICAgICAgJHtQcmltYXJ5QnV0dG9uKCLYq9io2Kog2b7bjNqv24zYsduMIiwgInN1Ym1pdEZvbGxvd1VwIiwgeyBkaXNhYmxlZDogIWNvbXBsZXRlIH0pfQogICAgPC9kaXY+YCl9CiAgPC9kaXY+YDsKfQpmdW5jdGlvbiBZZXNOb1JvdyhsYWJlbCwga2V5KSB7CiAgY29uc3QgdiA9IHN0YXRlLmZvcm1ba2V5XTsKICByZXR1cm4gYDxkaXY+PHAgY2xhc3M9InRleHQtc20gdGV4dC1zdG9uZS03MDAgbWItMiI+JHtlc2MobGFiZWwpfTwvcD4KICAgIDxkaXYgY2xhc3M9ImZsZXggZ2FwLTMiPgogICAgICA8YnV0dG9uIGRhdGEtYWN0aW9uPSJzZXRGb3JtIiBkYXRhLWtleT0iJHtrZXl9IiBkYXRhLXZhbHVlPSJ0cnVlIiBjbGFzcz0iZmxleC0xIHB5LTIuNSByb3VuZGVkLWxnIGZvbnQtc2VtaWJvbGQgYm9yZGVyICR7dj09PXRydWU/ImJnLXJvc2UtNjAwIHRleHQtd2hpdGUgYm9yZGVyLXJvc2UtNjAwIjoiYmctd2hpdGUgdGV4dC1zdG9uZS01MDAgYm9yZGVyLXN0b25lLTIwMCJ9Ij7YqNmE2Yc8L2J1dHRvbj4KICAgICAgPGJ1dHRvbiBkYXRhLWFjdGlvbj0ic2V0Rm9ybSIgZGF0YS1rZXk9IiR7a2V5fSIgZGF0YS12YWx1ZT0iZmFsc2UiIGNsYXNzPSJmbGV4LTEgcHktMi41IHJvdW5kZWQtbGcgZm9udC1zZW1pYm9sZCBib3JkZXIgJHt2PT09ZmFsc2U/ImJnLWVtZXJhbGQtNjAwIHRleHQtd2hpdGUgYm9yZGVyLWVtZXJhbGQtNjAwIjoiYmctd2hpdGUgdGV4dC1zdG9uZS01MDAgYm9yZGVyLXN0b25lLTIwMCJ9Ij7YrtuM2LE8L2J1dHRvbj4KICAgIDwvZGl2PgogIDwvZGl2PmA7Cn0KCi8qID09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PQogICDZhdiz24zYsSDaqdin2LHaqdmG2KfZhjog2YjYsdmI2K8g2Ygg2KrYutuM24zYsSDYsdmF2LIKICAgPT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09ICovCmZ1bmN0aW9uIHNjcmVlblN0YWZmTG9naW4oKSB7CiAgcmV0dXJuIGA8ZGl2IGNsYXNzPSJtYXgtdy1zbSBteC1hdXRvIHAtNSI+CiAgICAke1RvcEJhcigi2YjYsdmI2K8g2qnYp9ix2qnZhtin2YYiLCAiZ29MYW5kaW5nIil9JHtFcnJvckJveChzdGF0ZS5lcnJvck1zZyl9CiAgICAke0NhcmQoYDxkaXYgY2xhc3M9InAtNSBzcGFjZS15LTMiPgogICAgICA8ZGl2PjxsYWJlbCBjbGFzcz0idGV4dC14cyBmb250LXNlbWlib2xkIHRleHQtc3RvbmUtNTAwIj7Zhtin2YUg2qnYp9ix2KjYsduMPC9sYWJlbD48aW5wdXQgaWQ9InN0YWZmVXNlcm5hbWUiIGNsYXNzPSJ3LWZ1bGwgYm9yZGVyIGJvcmRlci1zdG9uZS0yMDAgcm91bmRlZC14bCBweC00IHB5LTMgbXQtMSIgLz48L2Rpdj4KICAgICAgPGRpdj48bGFiZWwgY2xhc3M9InRleHQteHMgZm9udC1zZW1pYm9sZCB0ZXh0LXN0b25lLTUwMCI+2LHZhdiyINi52KjZiNixPC9sYWJlbD48aW5wdXQgdHlwZT0icGFzc3dvcmQiIGlkPSJzdGFmZlBhc3N3b3JkIiBjbGFzcz0idy1mdWxsIGJvcmRlciBib3JkZXItc3RvbmUtMjAwIHJvdW5kZWQteGwgcHgtNCBweS0zIG10LTEiIC8+PC9kaXY+CiAgICAgICR7UHJpbWFyeUJ1dHRvbigi2YjYsdmI2K8iLCAic3RhZmZMb2dpblN1Ym1pdCIpfQogICAgICA8cCBjbGFzcz0idGV4dC14cyB0ZXh0LXN0b25lLTQwMCB0ZXh0LWNlbnRlciBwdC0yIj7Yp9mI2YTbjNmGINio2KfYsdifINmG2KfZhSDaqdin2LHYqNix24wgwqthZG1pbsK7INmIINix2YXYsiDCq2FkbWluMTIzNMK7IOKAlCDYqNmE2KfZgdin2LXZhNmHINio2LnYryDYp9iyINmI2LHZiNivINi52YjYtti0INqp2YbbjNivLjwvcD4KICAgIDwvZGl2PmApfQogIDwvZGl2PmA7Cn0KCmZ1bmN0aW9uIHNjcmVlbkNoYW5nZVBhc3N3b3JkKCkgewogIHJldHVybiBgPGRpdiBjbGFzcz0ibWF4LXctc20gbXgtYXV0byBwLTUiPgogICAgJHtUb3BCYXIoItiq2LrbjNuM2LEg2LHZhdiyINi52KjZiNixIiwgc3RhdGUuZm9yY2VkUHdDaGFuZ2UgPyBudWxsIDogImdvU3RhZmZEYXNoYm9hcmQiKX0KICAgICR7c3RhdGUuZm9yY2VkUHdDaGFuZ2UgPyBgPGRpdiBjbGFzcz0ibWItNCBwLTMgcm91bmRlZC14bCB0ZXh0LXNtIGJnLWFtYmVyLTEwMCB0ZXh0LWFtYmVyLTgwMCB0ZXh0LWNlbnRlciI+2KjYsdin24wg2KfZhdmG24zYqiDYrdiz2KfYqOKAjNiq2YjZhtiMINmE2LfZgdin2Ysg2YfZhduM2YYg2KfZhNin2YYg2LHZhdiyINix2Ygg2LnZiNi2INqp2YbbjNivLjwvZGl2PmAgOiAiIn0KICAgICR7RXJyb3JCb3goc3RhdGUuZXJyb3JNc2cpfQogICAgJHtDYXJkKGA8ZGl2IGNsYXNzPSJwLTUgc3BhY2UteS0zIj4KICAgICAgPGRpdj48bGFiZWwgY2xhc3M9InRleHQteHMgZm9udC1zZW1pYm9sZCB0ZXh0LXN0b25lLTUwMCI+2LHZhdiyINmB2LnZhNuMPC9sYWJlbD48aW5wdXQgdHlwZT0icGFzc3dvcmQiIGlkPSJjdXJQYXNzIiBjbGFzcz0idy1mdWxsIGJvcmRlciBib3JkZXItc3RvbmUtMjAwIHJvdW5kZWQteGwgcHgtNCBweS0zIG10LTEiIC8+PC9kaXY+CiAgICAgIDxkaXY+PGxhYmVsIGNsYXNzPSJ0ZXh0LXhzIGZvbnQtc2VtaWJvbGQgdGV4dC1zdG9uZS01MDAiPtix2YXYsiDYrNiv24zYryAo2K3Yr9in2YLZhCDbtiDaqdin2LHYp9qp2KrYsSk8L2xhYmVsPjxpbnB1dCB0eXBlPSJwYXNzd29yZCIgaWQ9Im5ld1Bhc3MiIGNsYXNzPSJ3LWZ1bGwgYm9yZGVyIGJvcmRlci1zdG9uZS0yMDAgcm91bmRlZC14bCBweC00IHB5LTMgbXQtMSIgLz48L2Rpdj4KICAgICAgJHtQcmltYXJ5QnV0dG9uKCLYq9io2Kog2LHZhdiyINis2K/bjNivIiwgInN1Ym1pdENoYW5nZVBhc3N3b3JkIil9CiAgICA8L2Rpdj5gKX0KICA8L2Rpdj5gOwp9CgovKiA9PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT0KICAg2K/Yp9i02KjZiNix2K8g2qnYp9ix2qnZhtin2YYKICAgPT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09ICovCmZ1bmN0aW9uIHNjcmVlblN0YWZmRGFzaGJvYXJkKCkgewogIGNvbnN0IHMgPSBzdGF0ZS5hZG1pbi5zdGF0cyB8fCB7fTsKICBjb25zdCBuYyA9IHN0YXRlLmFkbWluLm5vdGlmQ2VudGVyIHx8IHt9OwogIHJldHVybiBgPGRpdiBjbGFzcz0ibWF4LXctM3hsIG14LWF1dG8gcC01IHBiLTEwIj4KICAgIDxkaXYgY2xhc3M9ImZsZXggaXRlbXMtY2VudGVyIGp1c3RpZnktYmV0d2VlbiBtYi02Ij4KICAgICAgPGJ1dHRvbiBkYXRhLWFjdGlvbj0ic3RhZmZMb2dvdXQiIGNsYXNzPSJ0ZXh0LXN0b25lLTUwMCB0ZXh0LXNtIGZvbnQtc2VtaWJvbGQiPiYjODY3NDsg2K7YsdmI2Kw8L2J1dHRvbj4KICAgICAgPGgxIGNsYXNzPSJmb250LWJvbGQgdGV4dC1sZyB0ZXh0LXRlYWwtOTUwIj4mIzEyODczNzsg2b7ZhtmEINmF2K/bjNix24zYqiDZhdix2qnYsjwvaDE+CiAgICAgIDxidXR0b24gZGF0YS1hY3Rpb249ImdvQ2hhbmdlUGFzc3dvcmQiIGNsYXNzPSJ0ZXh0LXRlYWwtODAwIHRleHQtc20gZm9udC1zZW1pYm9sZCI+2KrYutuM24zYsSDYsdmF2LI8L2J1dHRvbj4KICAgIDwvZGl2PgogICAgJHtFcnJvckJveChzdGF0ZS5lcnJvck1zZyl9JHtUb2FzdChzdGF0ZS50b2FzdCl9CgogICAgPGRpdiBjbGFzcz0iZ3JpZCBncmlkLWNvbHMtMiBzbTpncmlkLWNvbHMtMyBnYXAtMiBtYi01Ij4KICAgICAgJHtHaG9zdEJ1dHRvbigiJiMxMjgxMDA7INin2YfYr9in2qnZhtmG2K/ar9in2YYiLCAiZ29Eb25vckxpc3QiKX0KICAgICAgJHtHaG9zdEJ1dHRvbigiJiMxMjgxOTc7INmG2YjYqNiq4oCM2YfYpyIsICJnb0FwcG9pbnRtZW50cyIpfQogICAgICAke0dob3N0QnV0dG9uKCImIzEyODI3Njsg2KfYudmE2KfZhuKAjNmH2KciLCAiZ29Ob3RpZkNlbnRlciIpfQogICAgICAke3N0YXRlLnN0YWZmLnJvbGUgPT09ICJhZG1pbiIgPyBHaG9zdEJ1dHRvbigiJiMxMjgyMDI7INiv2KfYtNio2YjYsdivIFBSIiwgImdvUHJEYXNoYm9hcmQiKSA6ICIifQogICAgICAke3N0YXRlLnN0YWZmLnJvbGUgPT09ICJhZG1pbiIgPyBHaG9zdEJ1dHRvbigiJiMxMjgxMDE7IENSTSIsICJnb0NybURhc2hib2FyZCIpIDogIiJ9CiAgICAgICR7c3RhdGUuc3RhZmYucm9sZSA9PT0gImFkbWluIiA/IEdob3N0QnV0dG9uKCImIzk4ODE7INiq2YbYuNuM2YXYp9iqIiwgImdvU2V0dGluZ3MiKSA6ICIifQogICAgPC9kaXY+CgogICAgPGRpdiBjbGFzcz0iZ3JpZCBncmlkLWNvbHMtMiBzbTpncmlkLWNvbHMtNCBnYXAtMyBtYi02Ij4KICAgICAgJHtTdGF0Q2FyZCgiJiMxMjgxMDA7IiwgItir2KjYquKAjNmG2KfZhSDYrNiv24zYryDYp9mF2LHZiNiyIiwgcy5uZXdSZWdpc3RyYXRpb25zKX0KICAgICAgJHtTdGF0Q2FyZCgiJiMxMjk1MTQ7IiwgItmF2YbYqti42LEg2KzZiNin2Kgg2KLYstmF2KfbjNi0Iiwgcy5hd2FpdGluZ0xhYil9CiAgICAgICR7U3RhdENhcmQoIiYjOTk4OTsiLCAi2b7ZhtmE4oCM2YfYp9uMINmB2LnYp9mEIiwgcy5hY3RpdmVQYW5lbHMpfQogICAgICAke1N0YXRDYXJkKCImIzEyODE5NzsiLCAi2YbZiNio2KrigIzZh9in24wg2KfZhdix2YjYsiIsIHMudG9kYXlzQXBwb2ludG1lbnRzKX0KICAgICAgJHtTdGF0Q2FyZCgiJiMxMjgxNjc7IiwgItin2YfYr9in2YfYp9uMINin2YbYrNin2YXigIzYtNiv2YciLCBzLnRvdGFsRG9uYXRpb25zKX0KICAgICAgJHtTdGF0Q2FyZCgiJiMxMTA4ODsiLCAi2K/Ysdi12K8g2LHYttin24zYqiIsIHMuc2F0aXNmYWN0aW9uUGVyY2VudCE9bnVsbCA/IGZhRGlnaXRzKHMuc2F0aXNmYWN0aW9uUGVyY2VudCkrIiUiIDogIi0iKX0KICAgIDwvZGl2PgoKICAgICR7Tm90aWZpY2F0aW9uQ2VudGVyUHJldmlldyhuYyl9CiAgPC9kaXY+YDsKfQoKZnVuY3Rpb24gTm90aWZpY2F0aW9uQ2VudGVyUHJldmlldyhuYykgewogIGNvbnN0IGFsZXJ0cyA9IG5jLmFsZXJ0cyB8fCBbXTsKICBjb25zdCBpdGVtcyA9IFsKICAgIC4uLihuYy5wZW5kaW5nTGFifHxbXSkuc2xpY2UoMCwzKS5tYXAoeCA9PiAoeyBpY29uOiImIzEyODMwOTsiLCB0ZXh0OmDZhtiq24zYrNmH4oCM24wg2KLYstmF2KfbjNi0ICR7eC5kb25vck5hbWV9INii2YXYp9iv2YfigIzbjCDYqtin24zbjNivYCwgcGhvbmU6eC5kb25vclBob25lIH0pKSwKICAgIC4uLihuYy5uZXdBcHBvaW50bWVudFJlcXVlc3RzfHxbXSkuc2xpY2UoMCwzKS5tYXAoeCA9PiAoeyBpY29uOiImIzEyODE5NzsiLCB0ZXh0OmDYr9ix2K7ZiNin2LPYqiDZhtmI2KjYqiDYrNiv24zYryDYp9iyICR7eC5kb25vck5hbWV9YCwgcGhvbmU6eC5kb25vclBob25lIH0pKSwKICAgIC4uLihuYy5kdWVSZW1pbmRlcnN8fFtdKS5zbGljZSgwLDMpLm1hcCh4ID0+ICh7IGljb246IiYjMTI4MjIyOyIsIHRleHQ6YNuM2KfYr9ii2YjYsTogJHt4LnR5cGV9IOKAlCAke3guZG9ub3JOYW1lfWAsIHBob25lOnguZG9ub3JQaG9uZSB9KSksCiAgICAuLi4obmMuZm9sbG93dXBzTmVlZGVkfHxbXSkuc2xpY2UoMCwzKS5tYXAoeCA9PiAoeyBpY29uOiImIzEwMDg0OyYjNjUwMzk7IiwgdGV4dDpg2b7bjNqv24zYsduMINm+2LMg2KfYsiDYp9mH2K/YpyDZhNin2LLZhSDYp9iz2Kog4oCUICR7eC5kb25vck5hbWV9YCwgcGhvbmU6eC5kb25vclBob25lIH0pKSwKICAgIC4uLihuYy5uZXdTdXJ2ZXlzfHxbXSkuc2xpY2UoMCwzKS5tYXAoeCA9PiAoeyBpY29uOiImIzExMDg4OyIsIHRleHQ6YNmG2LjYsdiz2YbYrNuMINis2K/bjNivINir2KjYqiDYtNivIOKAlCAke3guZG9ub3JOYW1lfWAsIHBob25lOnguZG9ub3JQaG9uZSB9KSksCiAgXTsKICBpZiAoYWxlcnRzLmxlbmd0aCA9PT0gMCAmJiBpdGVtcy5sZW5ndGggPT09IDApIHJldHVybiBDYXJkKGA8ZGl2IGNsYXNzPSJwLTYgdGV4dC1jZW50ZXIgdGV4dC1zbSB0ZXh0LXN0b25lLTQwMCI+2YHYudmE2KfZiyDaqdin2LHbjCDYr9ixINin2YbYqti42KfYsSDZhtuM2LPYqiDwn46JPC9kaXY+YCk7CiAgcmV0dXJuIGAKICAgICR7YWxlcnRzLmxlbmd0aCA+IDAgPyBDYXJkKGA8ZGl2IGNsYXNzPSJwLTQiPgogICAgICA8cCBjbGFzcz0idGV4dC14cyBmb250LWJvbGQgdGV4dC1yb3NlLTcwMCBtYi0zIj4mIzk4ODg7JiM2NTAzOTsg2YfYtNiv2KfYsdmH2KfbjCDZh9mI2LTZhdmG2K88L3A+CiAgICAgIDxkaXYgY2xhc3M9InNwYWNlLXktMiI+JHthbGVydHMuc2xpY2UoMCw4KS5tYXAoKGEpID0+IGAKICAgICAgICA8YnV0dG9uIGRhdGEtYWN0aW9uPSJvcGVuRG9ub3JCeVBob25lIiBkYXRhLXBob25lPSIke2VzYyhhLnBob25lKX0iIGNsYXNzPSJ3LWZ1bGwgdGV4dC1yaWdodCBwLTIuNSBiZy1yb3NlLTUwIHJvdW5kZWQtbGcgdGV4dC14cyB0ZXh0LXJvc2UtODAwIj4ke2VzYyhhLmRvbm9yTmFtZSl9IOKAlCAke2VzYyhhLmRldGFpbCl9PC9idXR0b24+CiAgICAgIGApLmpvaW4oIiIpfTwvZGl2PgogICAgPC9kaXY+YCwgIm1iLTQgYm9yZGVyLXJvc2UtMjAwIikgOiAiIn0KICAgICR7aXRlbXMubGVuZ3RoID4gMCA/IENhcmQoYDxkaXYgY2xhc3M9InAtNCI+CiAgICAgIDxwIGNsYXNzPSJ0ZXh0LXhzIGZvbnQtYm9sZCB0ZXh0LXRlYWwtODAwIG1iLTMiPiYjMTI4Mjc2OyDZhdix2qnYsiDYp9i52YTYp9mG4oCM2YfYpzwvcD4KICAgICAgPGRpdiBjbGFzcz0ic3BhY2UteS0yIj4ke2l0ZW1zLm1hcCgoaXQpID0+IGAKICAgICAgICA8YnV0dG9uIGRhdGEtYWN0aW9uPSJvcGVuRG9ub3JCeVBob25lIiBkYXRhLXBob25lPSIke2VzYyhpdC5waG9uZSl9IiBjbGFzcz0idy1mdWxsIHRleHQtcmlnaHQgcC0yLjUgYmctdGVhbC01MCByb3VuZGVkLWxnIHRleHQteHMgdGV4dC10ZWFsLTkwMCI+JHtpdC5pY29ufSAke2VzYyhpdC50ZXh0KX08L2J1dHRvbj4KICAgICAgYCkuam9pbigiIil9PC9kaXY+CiAgICAgIDxkaXYgY2xhc3M9Im10LTMiPiR7U21hbGxCdXR0b24oItmF2LTYp9mH2K/Zh+KAjNuMINmH2YXZhyIsICJnb05vdGlmQ2VudGVyIiwgeyB0b25lOiAic3RvbmUiIH0pfTwvZGl2PgogICAgPC9kaXY+YCkgOiAiIn0KICBgOwp9CgpmdW5jdGlvbiBzY3JlZW5Ob3RpZkNlbnRlcigpIHsKICBjb25zdCBuYyA9IHN0YXRlLmFkbWluLm5vdGlmQ2VudGVyIHx8IHt9OwogIHJldHVybiBgPGRpdiBjbGFzcz0ibWF4LXctMnhsIG14LWF1dG8gcC01IHBiLTEwIj4KICAgICR7VG9wQmFyKCLZhdix2qnYsiDYp9i52YTYp9mG4oCM2YfYpyIsICJnb1N0YWZmRGFzaGJvYXJkIil9CiAgICAke05vdGlmaWNhdGlvbkNlbnRlclByZXZpZXcoeyAuLi5uYywgcGVuZGluZ0xhYjogbmMucGVuZGluZ0xhYiwgbmV3QXBwb2ludG1lbnRSZXF1ZXN0czogbmMubmV3QXBwb2ludG1lbnRSZXF1ZXN0cywgZHVlUmVtaW5kZXJzOiBuYy5kdWVSZW1pbmRlcnMsIGZvbGxvd3Vwc05lZWRlZDogbmMuZm9sbG93dXBzTmVlZGVkLCBuZXdTdXJ2ZXlzOiBuYy5uZXdTdXJ2ZXlzIH0pfQogIDwvZGl2PmA7Cn0KCi8qID09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PQogICDZgdmH2LHYs9iqINin2YfYr9in2qnZhtmG2K/ar9in2YYgKyDYrNiz2KrYrNmICiAgID09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PSAqLwpmdW5jdGlvbiBzY3JlZW5Eb25vckxpc3QoKSB7CiAgY29uc3QgZG9ub3JzID0gc3RhdGUuYWRtaW4uZG9ub3JzIHx8IFtdOwogIHJldHVybiBgPGRpdiBjbGFzcz0ibWF4LXctMnhsIG14LWF1dG8gcC01IHBiLTEwIj4KICAgICR7VG9wQmFyKCLYp9mH2K/Yp9qp2YbZhtiv2q/Yp9mGIiwgImdvU3RhZmZEYXNoYm9hcmQiKX0KICAgICR7RXJyb3JCb3goc3RhdGUuZXJyb3JNc2cpfQogICAgPGRpdiBjbGFzcz0ibWItNCBmbGV4IGdhcC0yIj4KICAgICAgPGlucHV0IGlkPSJzZWFyY2hJbnB1dCIgdmFsdWU9IiR7ZXNjKHN0YXRlLmFkbWluLnF8fCIiKX0iIHBsYWNlaG9sZGVyPSLYrNiz2KrYrNmIINio2Kcg2YbYp9mFINuM2Kcg2LTZhdin2LHZhyDZhdmI2KjYp9uM2YQuLi4iIGNsYXNzPSJmbGV4LTEgYm9yZGVyIGJvcmRlci1zdG9uZS0yMDAgcm91bmRlZC14bCBweC00IHB5LTMiIC8+CiAgICAgICR7U21hbGxCdXR0b24oItis2LPYqtis2YgiLCAic2VhcmNoRG9ub3JzIiwgeyB0b25lOiAidGVhbCIgfSl9CiAgICA8L2Rpdj4KICAgICR7c3RhdGUuc3RhZmYucm9sZSA9PT0gImFkbWluIiA/IGA8ZGl2IGNsYXNzPSJtYi00Ij4ke1NtYWxsQnV0dG9uKCImIzEyODE5MDsg2K7YsdmI2KzbjCBFeGNlbCAoQ1NWKSIsICJleHBvcnRDc3YiLCB7IHRvbmU6ICJzdG9uZSIgfSl9PC9kaXY+YCA6ICIifQogICAgPGRpdiBjbGFzcz0ic3BhY2UteS0yIj4KICAgICAgJHtkb25vcnMubGVuZ3RoID09PSAwID8gYDxwIGNsYXNzPSJ0ZXh0LXNtIHRleHQtc3RvbmUtNDAwIHRleHQtY2VudGVyIHB5LTEwIj7Yp9mH2K/Yp9qp2YbZhtiv2YfigIzYp9uMINm+24zYr9inINmG2LTYrzwvcD5gIDogZG9ub3JzLm1hcCgoZCkgPT4gYAogICAgICAgIDxidXR0b24gZGF0YS1hY3Rpb249Im9wZW5Eb25vckJ5UGhvbmUiIGRhdGEtcGhvbmU9IiR7ZXNjKGQucGhvbmUpfSIgY2xhc3M9InctZnVsbCB0ZXh0LXJpZ2h0Ij4KICAgICAgICAgICR7Q2FyZChgPGRpdiBjbGFzcz0icC00IGZsZXggaXRlbXMtY2VudGVyIGp1c3RpZnktYmV0d2VlbiBob3Zlcjpib3JkZXItdGVhbC0zMDAiPgogICAgICAgICAgICA8ZGl2IGNsYXNzPSJmbGV4IGl0ZW1zLWNlbnRlciBnYXAtMyI+CiAgICAgICAgICAgICAgPGRpdiBjbGFzcz0idy0xMCBoLTEwIHJvdW5kZWQtZnVsbCBiZy10ZWFsLTkwMCB0ZXh0LXdoaXRlIGZsZXggaXRlbXMtY2VudGVyIGp1c3RpZnktY2VudGVyIGZvbnQtYm9sZCI+JHtlc2MoZC5maXJzdE5hbWUuY2hhckF0KDApKX08L2Rpdj4KICAgICAgICAgICAgICA8ZGl2PjxwIGNsYXNzPSJmb250LWJvbGQgdGV4dC10ZWFsLTk1MCI+JHtlc2MoZC5maXJzdE5hbWUpfSAke2VzYyhkLmxhc3ROYW1lKX08L3A+PHAgY2xhc3M9InRleHQteHMgdGV4dC1zdG9uZS00MDAiPiR7ZXNjKGQucGhvbmUpfSDCtyAke2ZhRGlnaXRzKGQuYXBwb2ludG1lbnRzLmZpbHRlcihhPT5hLmRvbmF0ZWQ9PT10cnVlKS5sZW5ndGgpfSDYp9mH2K/YpzwvcD48L2Rpdj4KICAgICAgICAgICAgPC9kaXY+CiAgICAgICAgICAgIDxkaXYgY2xhc3M9ImZsZXggaXRlbXMtY2VudGVyIGdhcC0yIj4KICAgICAgICAgICAgICAke2QuZmxhZ2dlZCA/IEJhZGdlKCLZvtuM2q/bjNix24wiLCJyb3NlIikgOiAiIn0KICAgICAgICAgICAgICAke0JhZGdlKFNUQVRVU19MQUJFTFNbZC5zdGF0dXNdfHxkLnN0YXR1cywgZC5zdGF0dXM9PT0iZG9uYXRlZCJ8fGQuc3RhdHVzPT09InJlYWR5Ij8iZW1lcmFsZCI6ZC5zdGF0dXM9PT0iYmxvY2tlZCI/InJvc2UiOiJzbGF0ZSIpfQogICAgICAgICAgICA8L2Rpdj4KICAgICAgICAgIDwvZGl2PmApfQogICAgICAgIDwvYnV0dG9uPgogICAgICBgKS5qb2luKCIiKX0KICAgIDwvZGl2PgogIDwvZGl2PmA7Cn0KCi8qID09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PQogICDYrNiy2KbbjNin2Kog2KfZh9iv2KfaqdmG2YbYr9mHIChDUk0pCiAgID09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PSAqLwpmdW5jdGlvbiBzY3JlZW5Eb25vckRldGFpbCgpIHsKICBjb25zdCBkID0gc3RhdGUuYWRtaW4uc2VsZWN0ZWREb25vcjsKICBpZiAoIWQpIHJldHVybiBgPGRpdiBjbGFzcz0icC0xMCB0ZXh0LWNlbnRlciB0ZXh0LXN0b25lLTQwMCI+2K/YsSDYrdin2YQg2KjYp9ix2q/YsNin2LHbjC4uLjwvZGl2PmA7CiAgcmV0dXJuIGA8ZGl2IGNsYXNzPSJtYXgtdy0yeGwgbXgtYXV0byBwLTUgcGItMTAiPgogICAgJHtUb3BCYXIoYCR7ZC5maXJzdE5hbWV9ICR7ZC5sYXN0TmFtZX1gLCAiZ29Eb25vckxpc3QiKX0KICAgICR7RXJyb3JCb3goc3RhdGUuZXJyb3JNc2cpfSR7VG9hc3Qoc3RhdGUudG9hc3QpfQoKICAgICR7Q2FyZChgPGRpdiBjbGFzcz0icC00Ij4KICAgICAgPGRpdiBjbGFzcz0iZmxleCBpdGVtcy1jZW50ZXIganVzdGlmeS1iZXR3ZWVuIG1iLTMiPgogICAgICAgIDxkaXY+PHAgY2xhc3M9InRleHQtc20gdGV4dC1zdG9uZS01MDAiPiR7ZXNjKGQucGhvbmUpfSDCtyAke2ZhRGlnaXRzKGQuYWdlKX0g2LPYp9mE2Yc8L3A+PHAgY2xhc3M9InRleHQteHMgdGV4dC1zdG9uZS00MDAiPti52LbZiNuM2Kog2KfYsiAke2ZtdERhdGUoZC5jcmVhdGVkQXQpfTwvcD48L2Rpdj4KICAgICAgICAke2QuZmxhZ2dlZCA/IEJhZGdlKCLZhtuM2KfYstmF2YbYryDZvtuM2q/bjNix24wiLCJyb3NlIikgOiAiIn0KICAgICAgPC9kaXY+CiAgICAgIDxsYWJlbCBjbGFzcz0idGV4dC14cyBmb250LXNlbWlib2xkIHRleHQtc3RvbmUtNTAwIj7ZiNi22LnbjNiqPC9sYWJlbD4KICAgICAgPHNlbGVjdCBkYXRhLWFjdGlvbj0iY2hhbmdlU3RhdHVzIiBjbGFzcz0idy1mdWxsIGJvcmRlciBib3JkZXItc3RvbmUtMjAwIHJvdW5kZWQteGwgcHgtNCBweS0zIG10LTEiPgogICAgICAgICR7T2JqZWN0LmVudHJpZXMoU1RBVFVTX0xBQkVMUykubWFwKChbayxsYWJlbF0pID0+IGA8b3B0aW9uIHZhbHVlPSIke2t9IiAke2Quc3RhdHVzPT09az8ic2VsZWN0ZWQiOiIifT4ke2xhYmVsfTwvb3B0aW9uPmApLmpvaW4oIiIpfQogICAgICA8L3NlbGVjdD4KICAgICAgPGRpdiBjbGFzcz0iZ3JpZCBncmlkLWNvbHMtMiBnYXAtMiBtdC0zIj4KICAgICAgICAke2Quc3RhdHVzID09PSAiYXdhaXRpbmdfbGFiIiA/IFNtYWxsQnV0dG9uKCLYqtin24zbjNivINmG2KrbjNis2YfigIzbjCDYotiy2YXYp9uM2LQiLCAiYXBwcm92ZUxhYiIsIHsgdG9uZTogImVtZXJhbGQiIH0pIDogIiJ9CiAgICAgICAgJHtzdGF0ZS5zdGFmZi5yb2xlID09PSAiYWRtaW4iID8gU21hbGxCdXR0b24oItmF2LPYr9mI2K/Ys9in2LLbjCIsICJibG9ja0Rvbm9yIiwgeyB0b25lOiAicm9zZSIgfSkgOiAiIn0KICAgICAgPC9kaXY+CiAgICA8L2Rpdj5gLCAibWItNCIpfQoKICAgICR7ZC5zdXJ2ZXkgPyBDYXJkKGA8ZGl2IGNsYXNzPSJwLTQiPgogICAgICA8cCBjbGFzcz0idGV4dC14cyBmb250LWJvbGQgdGV4dC10ZWFsLTgwMCBtYi0zIj7Zhtiq24zYrNmH4oCM24wg2YbYuNix2LPZhtis24wg2KfZiNmE24zZhiDZhdix2KfYrNi52Yc8L3A+CiAgICAgIDxkaXYgY2xhc3M9InRleHQteHMgdGV4dC1zdG9uZS02MDAgc3BhY2UteS0xIj4KICAgICAgICAke1NVUlZFWV9DQVRFR09SSUVTLm1hcCgoW2tleSxsYWJlbF0pID0+IGA8cD4ke2xhYmVsfTogPGI+JHtmYURpZ2l0cyhkLnN1cnZleVtrZXldKX0v27U8L2I+PC9wPmApLmpvaW4oIiIpfQogICAgICAgIDxwPtii2LTZhtin24zbjCDYqNinINmF2LHaqdiyOiA8Yj4ke2VzYyhkLnN1cnZleS5yZWZlcnJhbFNvdXJjZSl9PC9iPjwvcD4KICAgICAgICAke2Quc3VydmV5LmZyZWVUZXh0ID8gYDxwIGNsYXNzPSJpdGFsaWMgbXQtMiI+wqske2VzYyhkLnN1cnZleS5mcmVlVGV4dCl9wrs8L3A+YCA6ICIifQogICAgICA8L2Rpdj4KICAgIDwvZGl2PmAsICJtYi00IikgOiAiIn0KCiAgICAke0FwcG9pbnRtZW50c1NlY3Rpb24oZCl9CiAgICAke05vdGVzU2VjdGlvbihkKX0KICAgICR7UmVtaW5kZXJzU2VjdGlvbihkKX0KICAgICR7VGltZWxpbmVTZWN0aW9uKGQpfQogIDwvZGl2PmA7Cn0KCmZ1bmN0aW9uIEFwcG9pbnRtZW50c1NlY3Rpb24oZCkgewogIGNvbnN0IGFjdGl2ZSA9IGQuYXBwb2ludG1lbnRzLmZpbHRlcigoYSkgPT4gYS5zdGF0dXMgIT09ICJjYW5jZWxsZWQiICYmIGEuc3RhdHVzICE9PSAiY29tcGxldGVkIik7CiAgcmV0dXJuIENhcmQoYDxkaXYgY2xhc3M9InAtNCI+CiAgICA8cCBjbGFzcz0idGV4dC14cyBmb250LWJvbGQgdGV4dC10ZWFsLTgwMCBtYi0zIj7ZhtmI2KjYquKAjNmH2Kc8L3A+CiAgICAke2FjdGl2ZS5sZW5ndGggPT09IDAgPyBgPHAgY2xhc3M9InRleHQteHMgdGV4dC1zdG9uZS00MDAgbWItMiI+2YbZiNio2Kog2YHYudin2YTbjCDZhtuM2LPYqjwvcD5gIDogYWN0aXZlLm1hcCgoYSkgPT4gYAogICAgICA8ZGl2IGNsYXNzPSJiZy1zdG9uZS01MCByb3VuZGVkLXhsIHAtMyBtYi0yIj4KICAgICAgICA8cCBjbGFzcz0idGV4dC1zbSBmb250LXNlbWlib2xkIHRleHQtdGVhbC05NTAiPiR7Zm10RGF0ZVRpbWUoYS5jb25maXJtZWREYXRlfHxhLnJlcXVlc3RlZERhdGUpfTwvcD4KICAgICAgICA8cCBjbGFzcz0idGV4dC14cyB0ZXh0LXN0b25lLTQwMCBtYi0yIj4ke2Euc3RhdHVzPT09InJlcXVlc3RlZCI/Itiv2LEg2KfZhtiq2LjYp9ixINiq2KfbjNuM2K8iOmEuc3RhdHVzPT09ImNvbmZpcm1lZCI/Itiq2KfbjNuM2K/YtNiv2YciOmEuc3RhdHVzPT09InJlc2NoZWR1bGVkX2J5X2FkbWluIj8i2LLZhdin2YYg2KzYr9uM2K8g2b7bjNi02YbZh9in2K8g2LTYr9mHIjphLnN0YXR1c308L3A+CiAgICAgICAgPGRpdiBjbGFzcz0iZmxleCBmbGV4LXdyYXAgZ2FwLTIiPgogICAgICAgICAgJHthLnN0YXR1cz09PSJyZXF1ZXN0ZWQiID8gU21hbGxCdXR0b24oItiq2KfbjNuM2K8iLCAiY29uZmlybUFwcG9pbnRtZW50IiwgeyBkYXRhOntpZDphLmlkfSwgdG9uZToiZW1lcmFsZCIgfSkgOiAiIn0KICAgICAgICAgICR7U21hbGxCdXR0b24oItm+24zYtNmG2YfYp9ivINiy2YXYp9mGINiv24zar9ixIiwgInByb3Bvc2VSZXNjaGVkdWxlIiwgeyBkYXRhOntpZDphLmlkfSwgdG9uZToic3RvbmUiIH0pfQogICAgICAgICAgJHtTbWFsbEJ1dHRvbigi2YTYutmIIiwgImNhbmNlbEFwcHRBZG1pbiIsIHsgZGF0YTp7aWQ6YS5pZH0sIHRvbmU6InJvc2UiIH0pfQogICAgICAgICAgJHtTbWFsbEJ1dHRvbigi2KvYqNiqINmG2KrbjNis2YfigIzbjCDZhdix2KfYrNi52YciLCAib3Blbk91dGNvbWVGb3JtIiwgeyBkYXRhOntpZDphLmlkfSwgdG9uZToidGVhbCIgfSl9CiAgICAgICAgPC9kaXY+CiAgICAgIDwvZGl2PgogICAgYCkuam9pbigiIil9CiAgICA8ZGl2IGNsYXNzPSJtdC0zIHB0LTMgYm9yZGVyLXQgYm9yZGVyLXN0b25lLTEwMCI+CiAgICAgIDxwIGNsYXNzPSJ0ZXh0LXhzIHRleHQtc3RvbmUtNTAwIG1iLTIiPtir2KjYqiDZhtmI2KjYqiDYrNiv24zYryDYqNix2KfbjCDYp9uM2YYg2YHYsdivPC9wPgogICAgICA8ZGl2IGNsYXNzPSJncmlkIGdyaWQtY29scy0yIGdhcC0yIG1iLTIiPgogICAgICAgIDxpbnB1dCBpZD0iYXBwdERhdGUiIHR5cGU9ImRhdGUiIGNsYXNzPSJib3JkZXIgYm9yZGVyLXN0b25lLTIwMCByb3VuZGVkLWxnIHB4LTMgcHktMiB0ZXh0LXNtIiAvPgogICAgICAgIDxpbnB1dCBpZD0iYXBwdFRpbWUiIHR5cGU9InRpbWUiIGNsYXNzPSJib3JkZXIgYm9yZGVyLXN0b25lLTIwMCByb3VuZGVkLWxnIHB4LTMgcHktMiB0ZXh0LXNtIiAvPgogICAgICA8L2Rpdj4KICAgICAgJHtTbWFsbEJ1dHRvbigi2KvYqNiqINmIINiq2KfbjNuM2K8g2YbZiNio2KoiLCAiY3JlYXRlQXBwdEZvckRvbm9yIiwgeyB0b25lOiAidGVhbCIgfSl9CiAgICA8L2Rpdj4KICA8L2Rpdj5gLCAibWItNCIpOwp9CgpmdW5jdGlvbiBOb3Rlc1NlY3Rpb24oZCkgewogIHJldHVybiBDYXJkKGA8ZGl2IGNsYXNzPSJwLTQiPgogICAgPHAgY2xhc3M9InRleHQteHMgZm9udC1ib2xkIHRleHQtdGVhbC04MDAgbWItMyI+JiMxMjgyMjE7INuM2KfYr9iv2KfYtNiq4oCM2YfYp9uMINiv2KfYrtmE24wgKNmB2YLYtyDYqNix2KfbjCDaqdin2LHaqdmG2KfZhik8L3A+CiAgICA8dGV4dGFyZWEgaWQ9Im5vdGVJbnB1dCIgcm93cz0iMiIgcGxhY2Vob2xkZXI9ItmF2KvZhNin2Ys6INio2KfYsSDYp9mI2YQg2YXYsdin2KzYudmHINqp2LHYr9mHINmIINqp2YXbjCDZhdi22LfYsdioINio2YjYry4uLiIgY2xhc3M9InctZnVsbCBib3JkZXIgYm9yZGVyLXN0b25lLTIwMCByb3VuZGVkLWxnIHB4LTMgcHktMiB0ZXh0LXNtIG1iLTIiPjwvdGV4dGFyZWE+CiAgICAke1NtYWxsQnV0dG9uKCLYp9mB2LLZiNiv2YYg24zYp9iv2K/Yp9i02KoiLCAiYWRkTm90ZSIsIHsgdG9uZTogInRlYWwiIH0pfQogICAgPGRpdiBjbGFzcz0ibXQtMyBzcGFjZS15LTIiPgogICAgICAkeyhkLm5vdGVzfHxbXSkuc2xpY2UoKS5yZXZlcnNlKCkubWFwKChuKSA9PiBgCiAgICAgICAgPGRpdiBjbGFzcz0iYmctc3RvbmUtNTAgcm91bmRlZC1sZyBwLTIuNSB0ZXh0LXhzIj4KICAgICAgICAgIDxwIGNsYXNzPSJ0ZXh0LXN0b25lLTcwMCI+JHtlc2Mobi5ib2R5KX08L3A+CiAgICAgICAgICA8ZGl2IGNsYXNzPSJmbGV4IGl0ZW1zLWNlbnRlciBqdXN0aWZ5LWJldHdlZW4gbXQtMSB0ZXh0LXN0b25lLTQwMCI+CiAgICAgICAgICAgIDxzcGFuPiR7ZXNjKG4uYXV0aG9yVXNlcm5hbWUpfSDCtyAke2ZtdERhdGVTaG9ydChuLmNyZWF0ZWRBdCl9PC9zcGFuPgogICAgICAgICAgICAke3N0YXRlLnN0YWZmLnJvbGUgPT09ICJhZG1pbiIgPyBgPGJ1dHRvbiBkYXRhLWFjdGlvbj0iZGVsZXRlTm90ZSIgZGF0YS1pZD0iJHtuLmlkfSIgY2xhc3M9InRleHQtcm9zZS01MDAiPtit2LDZgTwvYnV0dG9uPmAgOiAiIn0KICAgICAgICAgIDwvZGl2PgogICAgICAgIDwvZGl2PgogICAgICBgKS5qb2luKCIiKX0KICAgIDwvZGl2PgogIDwvZGl2PmAsICJtYi00Iik7Cn0KCmZ1bmN0aW9uIFJlbWluZGVyc1NlY3Rpb24oZCkgewogIHJldHVybiBDYXJkKGA8ZGl2IGNsYXNzPSJwLTQiPgogICAgPHAgY2xhc3M9InRleHQteHMgZm9udC1ib2xkIHRleHQtdGVhbC04MDAgbWItMyI+JiM5MjAwOyDbjNin2K/YotmI2LHZh9in24wg2b7bjNqv24zYsduMPC9wPgogICAgPGRpdiBjbGFzcz0iZ3JpZCBncmlkLWNvbHMtMiBnYXAtMiBtYi0yIj4KICAgICAgPHNlbGVjdCBpZD0icmVtaW5kZXJUeXBlIiBjbGFzcz0iYm9yZGVyIGJvcmRlci1zdG9uZS0yMDAgcm91bmRlZC1sZyBweC0zIHB5LTIgdGV4dC1zbSI+CiAgICAgICAgJHtSRU1JTkRFUl9UWVBFUy5tYXAoKHQpID0+IGA8b3B0aW9uIHZhbHVlPSIke2VzYyh0KX0iPiR7ZXNjKHQpfTwvb3B0aW9uPmApLmpvaW4oIiIpfQogICAgICA8L3NlbGVjdD4KICAgICAgPGlucHV0IGlkPSJyZW1pbmRlckRhdGUiIHR5cGU9ImRhdGV0aW1lLWxvY2FsIiBjbGFzcz0iYm9yZGVyIGJvcmRlci1zdG9uZS0yMDAgcm91bmRlZC1sZyBweC0zIHB5LTIgdGV4dC1zbSIgLz4KICAgIDwvZGl2PgogICAgPHRleHRhcmVhIGlkPSJyZW1pbmRlck5vdGUiIHJvd3M9IjEiIHBsYWNlaG9sZGVyPSLYqtmI2LbbjNitICjYp9iu2KrbjNin2LHbjCkiIGNsYXNzPSJ3LWZ1bGwgYm9yZGVyIGJvcmRlci1zdG9uZS0yMDAgcm91bmRlZC1sZyBweC0zIHB5LTIgdGV4dC1zbSBtYi0yIj48L3RleHRhcmVhPgogICAgJHtTbWFsbEJ1dHRvbigi2KfZgdiy2YjYr9mGINuM2KfYr9ii2YjYsSIsICJhZGRSZW1pbmRlciIsIHsgdG9uZTogInRlYWwiIH0pfQogICAgPGRpdiBjbGFzcz0ibXQtMyBzcGFjZS15LTIiPgogICAgICAkeyhkLnJlbWluZGVyc3x8W10pLnNsaWNlKCkucmV2ZXJzZSgpLm1hcCgocikgPT4gYAogICAgICAgIDxkaXYgY2xhc3M9ImZsZXggaXRlbXMtY2VudGVyIGp1c3RpZnktYmV0d2VlbiBiZy1zdG9uZS01MCByb3VuZGVkLWxnIHAtMi41IHRleHQteHMgJHtyLmRvbmU/Im9wYWNpdHktNTAiOiIifSI+CiAgICAgICAgICA8c3Bhbj4ke2VzYyhyLnR5cGUpfSDigJQgJHtmbXREYXRlVGltZShyLmR1ZURhdGUpfSR7ci5ub3RlPyIg4oCUICIrZXNjKHIubm90ZSk6IiJ9PC9zcGFuPgogICAgICAgICAgJHshci5kb25lID8gYDxidXR0b24gZGF0YS1hY3Rpb249Im1hcmtSZW1pbmRlckRvbmUiIGRhdGEtaWQ9IiR7ci5pZH0iIGNsYXNzPSJ0ZXh0LWVtZXJhbGQtNjAwIGZvbnQtYm9sZCI+2KfZhtis2KfZhSDYtNivPC9idXR0b24+YCA6IGA8c3BhbiBjbGFzcz0idGV4dC1lbWVyYWxkLTYwMCI+4pyTPC9zcGFuPmB9CiAgICAgICAgPC9kaXY+CiAgICAgIGApLmpvaW4oIiIpfQogICAgPC9kaXY+CiAgPC9kaXY+YCwgIm1iLTQiKTsKfQoKZnVuY3Rpb24gVGltZWxpbmVTZWN0aW9uKGQpIHsKICByZXR1cm4gQ2FyZChgPGRpdiBjbGFzcz0icC00Ij4KICAgIDxwIGNsYXNzPSJ0ZXh0LXhzIGZvbnQtYm9sZCB0ZXh0LXRlYWwtODAwIG1iLTMiPiYjMTI4MzM3OyDYqtin2LHbjNiu2obZh+KAjNuMINqp2KfZhdmEINin2LHYqtio2KfYt9in2Ko8L3A+CiAgICA8ZGl2IGNsYXNzPSJzcGFjZS15LTIgYm9yZGVyLXItMiBib3JkZXItdGVhbC0xMDAgcHItMyI+CiAgICAgICR7KGQudGltZWxpbmV8fFtdKS5tYXAoKGUpID0+IGAKICAgICAgICA8ZGl2IGNsYXNzPSJ0ZXh0LXhzIj48cCBjbGFzcz0idGV4dC1zdG9uZS03MDAiPiR7ZXNjKGUubGFiZWwpfTwvcD48cCBjbGFzcz0idGV4dC1zdG9uZS00MDAiPiR7Zm10RGF0ZVRpbWUoZS5kYXRlKX08L3A+PC9kaXY+CiAgICAgIGApLmpvaW4oIiIpfQogICAgPC9kaXY+CiAgPC9kaXY+YCk7Cn0KCi8qID09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PQogICDZhdiv24zYsduM2Kog2YbZiNio2KrigIzZh9inCiAgID09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PSAqLwpmdW5jdGlvbiBzY3JlZW5BcHBvaW50bWVudHMoKSB7CiAgY29uc3QgbGlzdCA9IHN0YXRlLmFkbWluLmFwcG9pbnRtZW50cyB8fCBbXTsKICBjb25zdCBkYXRlID0gc3RhdGUuYWRtaW4uc2xvdERhdGUgfHwgdG9kYXlJU09EYXRlKCk7CiAgY29uc3Qgc2xvdHMgPSBzdGF0ZS5hZG1pbi5zbG90cyB8fCBbXTsKICByZXR1cm4gYDxkaXYgY2xhc3M9Im1heC13LTJ4bCBteC1hdXRvIHAtNSBwYi0xMCI+CiAgICAke1RvcEJhcigi2YXYr9uM2LHbjNiqINmG2YjYqNiq4oCM2YfYpyIsICJnb1N0YWZmRGFzaGJvYXJkIil9CiAgICAke0Vycm9yQm94KHN0YXRlLmVycm9yTXNnKX0ke1RvYXN0KHN0YXRlLnRvYXN0KX0KICAgICR7Q2FyZChgPGRpdiBjbGFzcz0icC00IG1iLTQiPgogICAgICA8cCBjbGFzcz0idGV4dC14cyBmb250LWJvbGQgdGV4dC10ZWFsLTgwMCBtYi0yIj7YuNix2YHbjNiqINix2YjYsjwvcD4KICAgICAgPGRpdiBjbGFzcz0iZmxleCBnYXAtMiBtYi0zIj4KICAgICAgICA8aW5wdXQgaWQ9InNsb3REYXRlSW5wdXQiIHR5cGU9ImRhdGUiIHZhbHVlPSIke2RhdGV9IiBjbGFzcz0iZmxleC0xIGJvcmRlciBib3JkZXItc3RvbmUtMjAwIHJvdW5kZWQtbGcgcHgtMyBweS0yIHRleHQtc20iIC8+CiAgICAgICAgJHtTbWFsbEJ1dHRvbigi2YbZhdin24zYtCIsICJsb2FkQWRtaW5TbG90cyIsIHsgdG9uZTogInRlYWwiIH0pfQogICAgICA8L2Rpdj4KICAgICAgPGRpdiBjbGFzcz0iZ3JpZCBncmlkLWNvbHMtNCBnYXAtMiI+CiAgICAgICAgJHtzbG90cy5tYXAoKHMpID0+IGA8ZGl2IGNsYXNzPSJ0ZXh0LWNlbnRlciBwLTIgcm91bmRlZC1sZyB0ZXh0LXhzICR7cy5hdmFpbGFibGU/ImJnLWVtZXJhbGQtNTAgdGV4dC1lbWVyYWxkLTcwMCI6ImJnLXJvc2UtNTAgdGV4dC1yb3NlLTYwMCJ9Ij4ke3MudGltZX08YnIvPiR7ZmFEaWdpdHMocy51c2VkKX0vJHtmYURpZ2l0cyhzLmNhcGFjaXR5KX08L2Rpdj5gKS5qb2luKCIiKX0KICAgICAgPC9kaXY+CiAgICA8L2Rpdj5gKX0KICAgIDxwIGNsYXNzPSJ0ZXh0LXhzIGZvbnQtYm9sZCB0ZXh0LXN0b25lLTQwMCBtYi0yIj7ZhtmI2KjYquKAjNmH2KfbjCDZvtuM2LTigIzYsdmIPC9wPgogICAgPGRpdiBjbGFzcz0ic3BhY2UteS0yIj4KICAgICAgJHtsaXN0Lmxlbmd0aD09PTAgPyBgPHAgY2xhc3M9InRleHQtc20gdGV4dC1zdG9uZS00MDAgdGV4dC1jZW50ZXIgcHktMTAiPtmG2YjYqNiq24wg2KvYqNiqINmG2LTYr9mHPC9wPmAgOiBsaXN0Lm1hcCgoYSkgPT4gYAogICAgICAgIDxidXR0b24gZGF0YS1hY3Rpb249Im9wZW5Eb25vckJ5UGhvbmUiIGRhdGEtcGhvbmU9IiR7ZXNjKGEuZG9ub3JQaG9uZSl9IiBjbGFzcz0idy1mdWxsIHRleHQtcmlnaHQiPgogICAgICAgICAgJHtDYXJkKGA8ZGl2IGNsYXNzPSJwLTMuNSBmbGV4IGl0ZW1zLWNlbnRlciBqdXN0aWZ5LWJldHdlZW4iPgogICAgICAgICAgICA8ZGl2PjxwIGNsYXNzPSJ0ZXh0LXNtIGZvbnQtc2VtaWJvbGQgdGV4dC10ZWFsLTk1MCI+JHtlc2MoYS5kb25vck5hbWUpfTwvcD48cCBjbGFzcz0idGV4dC14cyB0ZXh0LXN0b25lLTQwMCI+JHtmbXREYXRlVGltZShhLmNvbmZpcm1lZERhdGV8fGEucmVxdWVzdGVkRGF0ZSl9PC9wPjwvZGl2PgogICAgICAgICAgICAke0JhZGdlKGEuc3RhdHVzPT09InJlcXVlc3RlZCI/Itiv2LEg2KfZhtiq2LjYp9ixIjphLnN0YXR1cz09PSJjb25maXJtZWQiPyLYqtin24zbjNiv2LTYr9mHIjphLnN0YXR1cywgYS5zdGF0dXM9PT0iY29uZmlybWVkIj8iZW1lcmFsZCI6ImFtYmVyIil9CiAgICAgICAgICA8L2Rpdj5gKX0KICAgICAgICA8L2J1dHRvbj4KICAgICAgYCkuam9pbigiIil9CiAgICA8L2Rpdj4KICA8L2Rpdj5gOwp9CgovKiA9PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT0KICAg2KrZhti424zZhdin2Kog2YXYsdqp2LIKICAgPT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09ICovCmZ1bmN0aW9uIHNjcmVlblNldHRpbmdzKCkgewogIGNvbnN0IHMgPSBzdGF0ZS5hZG1pbi5zZXR0aW5ncyB8fCB7fTsKICBjb25zdCB0ID0gcy5zbXNUZW1wbGF0ZXMgfHwge307CiAgcmV0dXJuIGA8ZGl2IGNsYXNzPSJtYXgtdy1zbSBteC1hdXRvIHAtNSBwYi0xMCI+CiAgICAke1RvcEJhcigi2KrZhti424zZhdin2Kog2YXYsdqp2LIiLCAiZ29TdGFmZkRhc2hib2FyZCIpfSR7VG9hc3Qoc3RhdGUudG9hc3QpfQogICAgJHtDYXJkKGA8ZGl2IGNsYXNzPSJwLTUgc3BhY2UteS00Ij4KICAgICAgPHAgY2xhc3M9InRleHQteHMgZm9udC1ib2xkIHRleHQtdGVhbC04MDAiPtiq2YbYuNuM2YXYp9iqINi52YXZiNmF24w8L3A+CiAgICAgIDxkaXY+PGxhYmVsIGNsYXNzPSJ0ZXh0LXhzIHRleHQtc3RvbmUtNTAwIj7Zhtin2YUg2YXYsdqp2LI8L2xhYmVsPjxpbnB1dCBpZD0ic2V0Q2VudGVyTmFtZSIgdmFsdWU9IiR7ZXNjKHMuY2VudGVyTmFtZXx8IiIpfSIgY2xhc3M9InctZnVsbCBib3JkZXIgYm9yZGVyLXN0b25lLTIwMCByb3VuZGVkLXhsIHB4LTQgcHktMyBtdC0xIiAvPjwvZGl2PgogICAgICA8ZGl2PjxsYWJlbCBjbGFzcz0idGV4dC14cyB0ZXh0LXN0b25lLTUwMCI+2YHYp9i12YTZh+KAjNuMINmF2KzYp9iyINio24zZhiDYr9mIINin2YfYr9inICjYsdmI2LIpPC9sYWJlbD48aW5wdXQgaWQ9InNldEdhcERheXMiIHR5cGU9Im51bWJlciIgbWluPSIxIiB2YWx1ZT0iJHtNYXRoLnJvdW5kKChzLm1pbkdhcEhvdXJzfHwyNDApLzI0KX0iIGNsYXNzPSJ3LWZ1bGwgYm9yZGVyIGJvcmRlci1zdG9uZS0yMDAgcm91bmRlZC14bCBweC00IHB5LTMgbXQtMSIgLz48L2Rpdj4KICAgICAgPGRpdiBjbGFzcz0iZ3JpZCBncmlkLWNvbHMtMiBnYXAtMyI+CiAgICAgICAgPGRpdj48bGFiZWwgY2xhc3M9InRleHQteHMgdGV4dC1zdG9uZS01MDAiPtix2YjYstmH2KfbjCDZvtuM2q/bjNix24wg2b7YsyDYp9iyINin2YfYr9inPC9sYWJlbD48aW5wdXQgaWQ9InNldEZvbGxvd0RheXMiIHR5cGU9Im51bWJlciIgbWluPSIxIiB2YWx1ZT0iJHtzLmZvbGxvd1VwRGF5c3x8MX0iIGNsYXNzPSJ3LWZ1bGwgYm9yZGVyIGJvcmRlci1zdG9uZS0yMDAgcm91bmRlZC14bCBweC00IHB5LTMgbXQtMSIgLz48L2Rpdj4KICAgICAgICA8ZGl2PjxsYWJlbCBjbGFzcz0idGV4dC14cyB0ZXh0LXN0b25lLTUwMCI+2K/Zgdi52KfYqiDZvtuM2q/bjNix24wg2K/YsSDYsdmI2LI8L2xhYmVsPjxpbnB1dCBpZD0ic2V0Rm9sbG93RnJlcSIgdHlwZT0ibnVtYmVyIiBtaW49IjEiIHZhbHVlPSIke3MuZm9sbG93VXBGcmVxdWVuY3lQZXJEYXl8fDF9IiBjbGFzcz0idy1mdWxsIGJvcmRlciBib3JkZXItc3RvbmUtMjAwIHJvdW5kZWQteGwgcHgtNCBweS0zIG10LTEiIC8+PC9kaXY+CiAgICAgIDwvZGl2PgogICAgICA8ZGl2IGNsYXNzPSJncmlkIGdyaWQtY29scy0yIGdhcC0zIj4KICAgICAgICA8ZGl2PjxsYWJlbCBjbGFzcz0idGV4dC14cyB0ZXh0LXN0b25lLTUwMCI+2LPYp9i52Kog2LTYsdmI2Lkg2b7YsNuM2LHYtDwvbGFiZWw+PGlucHV0IGlkPSJzZXRTdGFydEhvdXIiIHR5cGU9InRpbWUiIHZhbHVlPSIke3MucmVjZXB0aW9uU3RhcnRIb3VyfHwiMDk6MDAifSIgY2xhc3M9InctZnVsbCBib3JkZXIgYm9yZGVyLXN0b25lLTIwMCByb3VuZGVkLXhsIHB4LTQgcHktMyBtdC0xIiAvPjwvZGl2PgogICAgICAgIDxkaXY+PGxhYmVsIGNsYXNzPSJ0ZXh0LXhzIHRleHQtc3RvbmUtNTAwIj7Ys9in2LnYqiDZvtin24zYp9mGINm+2LDbjNix2LQ8L2xhYmVsPjxpbnB1dCBpZD0ic2V0RW5kSG91ciIgdHlwZT0idGltZSIgdmFsdWU9IiR7cy5yZWNlcHRpb25FbmRIb3VyfHwiMTc6MDAifSIgY2xhc3M9InctZnVsbCBib3JkZXIgYm9yZGVyLXN0b25lLTIwMCByb3VuZGVkLXhsIHB4LTQgcHktMyBtdC0xIiAvPjwvZGl2PgogICAgICA8L2Rpdj4KICAgICAgPGRpdj48bGFiZWwgY2xhc3M9InRleHQteHMgdGV4dC1zdG9uZS01MDAgbWItMiBibG9jayI+2LHZiNiy2YfYp9uMINiq2LnYt9uM2YTbjCDZh9mB2Krar9uMPC9sYWJlbD4KICAgICAgICA8ZGl2IGNsYXNzPSJncmlkIGdyaWQtY29scy00IGdhcC0yIj4ke1dFRUtEQVlfTEFCRUxTLm1hcCgobGFiZWwsaWR4KSA9PiBgCiAgICAgICAgICA8YnV0dG9uIGRhdGEtYWN0aW9uPSJ0b2dnbGVDbG9zZWREYXkiIGRhdGEtZGF5PSIke2lkeH0iIGNsYXNzPSJweS0yIHJvdW5kZWQtbGcgdGV4dC14cyBmb250LXNlbWlib2xkIGJvcmRlciAkeyhzLmNsb3NlZFdlZWtkYXlzfHxbXSkuaW5jbHVkZXMoaWR4KT8iYmctcm9zZS02MDAgdGV4dC13aGl0ZSBib3JkZXItcm9zZS02MDAiOiJiZy13aGl0ZSBib3JkZXItc3RvbmUtMjAwIHRleHQtc3RvbmUtNjAwIn0iPiR7bGFiZWx9PC9idXR0b24+CiAgICAgICAgYCkuam9pbigiIil9PC9kaXY+CiAgICAgIDwvZGl2PgogICAgICA8ZGl2PjxsYWJlbCBjbGFzcz0idGV4dC14cyB0ZXh0LXN0b25lLTUwMCI+2KrYudi324zZhNin2Kog2LHYs9mF24wv2KfYrtiq2LXYp9i124wgKNmH2LEg2KrYp9ix24zYriDYr9ixINuM2qkg2K7Yt9iMINmB2LHZhdiqIFlZWVktTU0tREQpPC9sYWJlbD4KICAgICAgICA8dGV4dGFyZWEgaWQ9InNldEhvbGlkYXlzIiByb3dzPSIzIiBjbGFzcz0idy1mdWxsIGJvcmRlciBib3JkZXItc3RvbmUtMjAwIHJvdW5kZWQteGwgcHgtNCBweS0zIG10LTEiPiR7KHMuaG9saWRheXN8fFtdKS5qb2luKCJcbiIpfTwvdGV4dGFyZWE+CiAgICAgIDwvZGl2PgoKICAgICAgPHAgY2xhc3M9InRleHQteHMgZm9udC1ib2xkIHRleHQtdGVhbC04MDAgcHQtMiI+2YbZiNio2KrigIzYr9mH24w8L3A+CiAgICAgIDxkaXY+PGxhYmVsIGNsYXNzPSJ0ZXh0LXhzIHRleHQtc3RvbmUtNTAwIG1iLTIgYmxvY2siPtit2KfZhNiqINmG2YjYqNiq4oCM2K/Zh9uMPC9sYWJlbD4KICAgICAgICA8ZGl2IGNsYXNzPSJncmlkIGdyaWQtY29scy0yIGdhcC0yIj4KICAgICAgICAgIDxidXR0b24gZGF0YS1hY3Rpb249InNldEFwcG9pbnRtZW50TW9kZSIgZGF0YS1tb2RlPSJhdXRvIiBjbGFzcz0icHktMi41IHJvdW5kZWQtbGcgdGV4dC1zbSBib3JkZXIgJHtzLmFwcG9pbnRtZW50TW9kZT09PSJhdXRvIj8iYmctdGVhbC04MDAgdGV4dC13aGl0ZSBib3JkZXItdGVhbC04MDAiOiJiZy13aGl0ZSBib3JkZXItc3RvbmUtMjAwIn0iPtiu2YjYr9qp2KfYsTwvYnV0dG9uPgogICAgICAgICAgPGJ1dHRvbiBkYXRhLWFjdGlvbj0ic2V0QXBwb2ludG1lbnRNb2RlIiBkYXRhLW1vZGU9Im1hbnVhbCIgY2xhc3M9InB5LTIuNSByb3VuZGVkLWxnIHRleHQtc20gYm9yZGVyICR7cy5hcHBvaW50bWVudE1vZGU9PT0ibWFudWFsIj8iYmctdGVhbC04MDAgdGV4dC13aGl0ZSBib3JkZXItdGVhbC04MDAiOiJiZy13aGl0ZSBib3JkZXItc3RvbmUtMjAwIn0iPtiq2KPbjNuM2K8g2K/Ys9iq24w8L2J1dHRvbj4KICAgICAgICA8L2Rpdj4KICAgICAgPC9kaXY+CiAgICAgIDxkaXY+PGxhYmVsIGNsYXNzPSJ0ZXh0LXhzIHRleHQtc3RvbmUtNTAwIj7YuNix2YHbjNiqINmH2LEg2LPYp9i52KogKNmG2YHYsSk8L2xhYmVsPjxpbnB1dCBpZD0ic2V0Q2FwYWNpdHkiIHR5cGU9Im51bWJlciIgbWluPSIxIiB2YWx1ZT0iJHtzLmhvdXJseUNhcGFjaXR5fHw0fSIgY2xhc3M9InctZnVsbCBib3JkZXIgYm9yZGVyLXN0b25lLTIwMCByb3VuZGVkLXhsIHB4LTQgcHktMyBtdC0xIiAvPjwvZGl2PgogICAgICA8ZGl2PjxsYWJlbCBjbGFzcz0idGV4dC14cyB0ZXh0LXN0b25lLTUwMCI+2YfYtNiv2KfYsSDYudiv2YUg2YXYsdin2KzYudmHINio2LnYryDYp9iyICjYsdmI2LIpPC9sYWJlbD48aW5wdXQgaWQ9InNldE5vU2hvdyIgdHlwZT0ibnVtYmVyIiBtaW49IjEiIHZhbHVlPSIke3Mubm9TaG93QWxlcnREYXlzfHwxNH0iIGNsYXNzPSJ3LWZ1bGwgYm9yZGVyIGJvcmRlci1zdG9uZS0yMDAgcm91bmRlZC14bCBweC00IHB5LTMgbXQtMSIgLz48L2Rpdj4KCiAgICAgICR7UHJpbWFyeUJ1dHRvbigi2LDYrtuM2LHZh+KAjNuMINiq2YbYuNuM2YXYp9iqIiwgInNhdmVTZXR0aW5ncyIpfQogICAgPC9kaXY+YCwgIm1iLTUiKX0KCiAgICAke0NhcmQoYDxkaXYgY2xhc3M9InAtNSBzcGFjZS15LTMiPgogICAgICA8cCBjbGFzcz0idGV4dC14cyBmb250LWJvbGQgdGV4dC10ZWFsLTgwMCI+2YXYqtmGINm+24zYp9mF2qnigIzZh9inICjZgtin2KjZhCDZiNuM2LHYp9uM2LQpPC9wPgogICAgICAke1sicmVnaXN0cmF0aW9uIiwicGFuZWxBY3RpdmF0ZWQiLCJhcHBvaW50bWVudENvbmZpcm1lZCIsImFwcG9pbnRtZW50UmVtaW5kZXIiLCJwb3N0RG9uYXRpb25Gb2xsb3d1cCIsInJlYm9va2luZ0VuYWJsZWQiXS5tYXAoKGtleSkgPT4gYAogICAgICAgIDxkaXY+PGxhYmVsIGNsYXNzPSJ0ZXh0LXhzIHRleHQtc3RvbmUtNTAwIj4ke3Ntc1RlbXBsYXRlTGFiZWwoa2V5KX08L2xhYmVsPgogICAgICAgICAgPHRleHRhcmVhIGlkPSJ0cGxfJHtrZXl9IiByb3dzPSIyIiBjbGFzcz0idy1mdWxsIGJvcmRlciBib3JkZXItc3RvbmUtMjAwIHJvdW5kZWQteGwgcHgtNCBweS0zIG10LTEiPiR7ZXNjKHRba2V5XXx8IiIpfTwvdGV4dGFyZWE+CiAgICAgICAgPC9kaXY+CiAgICAgIGApLmpvaW4oIiIpfQogICAgICA8cCBjbGFzcz0idGV4dC14cyB0ZXh0LXN0b25lLTQwMCI+2YXbjOKAjNiq2YjZhtuM2K8g2KfYsiB7bmFtZX0g2Ygge2NlbnRlck5hbWV9INmIIHtkYXRlfSDYr9in2K7ZhCDZhdiq2YYg2KfYs9iq2YHYp9iv2Ycg2qnZhtuM2K8uPC9wPgogICAgICAke1ByaW1hcnlCdXR0b24oItiw2K7bjNix2YfigIzbjCDZhdiq2YYg2b7bjNin2YXaqeKAjNmH2KciLCAic2F2ZVNtc1RlbXBsYXRlcyIpfQogICAgPC9kaXY+YCwgIm1iLTUiKX0KCiAgICAke3N0YXRlLnN0YWZmLnJvbGUgPT09ICJhZG1pbiIgPyBHaG9zdEJ1dHRvbigiJiMxMjgxMDA7INmF2K/bjNix24zYqiDaqdin2LHaqdmG2KfZhiIsICJnb1N0YWZmVXNlcnMiKSA6ICIifQogIDwvZGl2PmA7Cn0KZnVuY3Rpb24gc21zVGVtcGxhdGVMYWJlbChrZXkpIHsKICByZXR1cm4geyByZWdpc3RyYXRpb246Itm+24zYp9mFINir2KjYquKAjNmG2KfZhSIsIHBhbmVsQWN0aXZhdGVkOiLZvtuM2KfZhSDZgdi52KfZhCDYtNiv2YYg2b7ZhtmEIiwgYXBwb2ludG1lbnRDb25maXJtZWQ6Itm+24zYp9mFINiq2KPbjNuM2K8g2YbZiNio2KoiLAogICAgYXBwb2ludG1lbnRSZW1pbmRlcjoi2b7bjNin2YUg24zYp9iv2KLZiNix24wg2YbZiNio2KoiLCBwb3N0RG9uYXRpb25Gb2xsb3d1cDoi2b7bjNin2YUg2b7bjNqv24zYsduMINio2LnYryDYp9iyINin2YfYr9inIiwgcmVib29raW5nRW5hYmxlZDoi2b7bjNin2YUg2YHYudin2YQg2LTYr9mGINix2LLYsdmIINmF2KzYr9ivIiB9W2tleV0gfHwga2V5Owp9CgovKiA9PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT0KICAg2YXYr9uM2LHbjNiqINqp2KfYsdqp2YbYp9mGCiAgID09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PSAqLwpmdW5jdGlvbiBzY3JlZW5TdGFmZlVzZXJzKCkgewogIGNvbnN0IHVzZXJzID0gc3RhdGUuYWRtaW4uc3RhZmZMaXN0IHx8IFtdOwogIHJldHVybiBgPGRpdiBjbGFzcz0ibWF4LXctc20gbXgtYXV0byBwLTUiPgogICAgJHtUb3BCYXIoItmF2K/bjNix24zYqiDaqdin2LHaqdmG2KfZhiIsICJnb1NldHRpbmdzIil9JHtFcnJvckJveChzdGF0ZS5lcnJvck1zZyl9JHtUb2FzdChzdGF0ZS50b2FzdCl9CiAgICAke0NhcmQoYDxkaXYgY2xhc3M9InAtNSBzcGFjZS15LTMgbWItNSI+CiAgICAgIDxwIGNsYXNzPSJ0ZXh0LXhzIGZvbnQtYm9sZCB0ZXh0LXRlYWwtODAwIj7Yp9mB2LLZiNiv2YYg2qnYp9ix2YXZhtivINis2K/bjNivPC9wPgogICAgICA8aW5wdXQgaWQ9Im5ld1N0YWZmVXNlcm5hbWUiIHBsYWNlaG9sZGVyPSLZhtin2YUg2qnYp9ix2KjYsduMIiBjbGFzcz0idy1mdWxsIGJvcmRlciBib3JkZXItc3RvbmUtMjAwIHJvdW5kZWQteGwgcHgtNCBweS0zIiAvPgogICAgICA8aW5wdXQgaWQ9Im5ld1N0YWZmUGFzc3dvcmQiIHR5cGU9InBhc3N3b3JkIiBwbGFjZWhvbGRlcj0i2LHZhdiyINmF2YjZgtiqICjYrdiv2KfZgtmEINu2INqp2KfYsdin2qnYqtixKSIgY2xhc3M9InctZnVsbCBib3JkZXIgYm9yZGVyLXN0b25lLTIwMCByb3VuZGVkLXhsIHB4LTQgcHktMyIgLz4KICAgICAgPHNlbGVjdCBpZD0ibmV3U3RhZmZSb2xlIiBjbGFzcz0idy1mdWxsIGJvcmRlciBib3JkZXItc3RvbmUtMjAwIHJvdW5kZWQteGwgcHgtNCBweS0zIj4KICAgICAgICA8b3B0aW9uIHZhbHVlPSJzdGFmZiI+2qnYp9ix2YXZhtivINi52KfYr9uMPC9vcHRpb24+PG9wdGlvbiB2YWx1ZT0iYWRtaW4iPtmF2K/bjNixPC9vcHRpb24+CiAgICAgIDwvc2VsZWN0PgogICAgICAke1ByaW1hcnlCdXR0b24oItin2YHYstmI2K/ZhiIsICJhZGRTdGFmZlVzZXIiKX0KICAgIDwvZGl2PmApfQogICAgPGRpdiBjbGFzcz0ic3BhY2UteS0yIj4KICAgICAgJHt1c2Vycy5tYXAoKHUpID0+IGAke0NhcmQoYDxkaXYgY2xhc3M9InAtMy41IGZsZXggaXRlbXMtY2VudGVyIGp1c3RpZnktYmV0d2VlbiI+CiAgICAgICAgPGRpdj48cCBjbGFzcz0iZm9udC1zZW1pYm9sZCB0ZXh0LXNtIHRleHQtdGVhbC05NTAiPiR7ZXNjKHUudXNlcm5hbWUpfTwvcD48cCBjbGFzcz0idGV4dC14cyB0ZXh0LXN0b25lLTQwMCI+JHt1LnJvbGU9PT0iYWRtaW4iPyLZhdiv24zYsSI6Itqp2KfYsdmF2YbYryJ9JHt1LmJsb2NrZWQ/IiDCtyDZhdiz2K/ZiNivIjoiIn08L3A+PC9kaXY+CiAgICAgICAgPGRpdiBjbGFzcz0iZmxleCBnYXAtMiI+CiAgICAgICAgICAke3UuaWQgIT09IHN0YXRlLnN0YWZmLmlkID8gYDxidXR0b24gZGF0YS1hY3Rpb249InRvZ2dsZUJsb2NrU3RhZmYiIGRhdGEtaWQ9IiR7dS5pZH0iIGRhdGEtYmxvY2tlZD0iJHshdS5ibG9ja2VkfSIgY2xhc3M9InRleHQteHMgdGV4dC1hbWJlci02MDAgZm9udC1ib2xkIj4ke3UuYmxvY2tlZD8i2LHZgdi5INmF2LPYr9mI2K/bjCI6ItmF2LPYr9mI2K8g2qnZhiJ9PC9idXR0b24+CiAgICAgICAgICA8YnV0dG9uIGRhdGEtYWN0aW9uPSJkZWxldGVTdGFmZlVzZXIiIGRhdGEtaWQ9IiR7dS5pZH0iIGNsYXNzPSJ0ZXh0LXhzIHRleHQtcm9zZS02MDAgZm9udC1ib2xkIj7Yrdiw2YE8L2J1dHRvbj5gIDogYDxzcGFuIGNsYXNzPSJ0ZXh0LXhzIHRleHQtc3RvbmUtMzAwIj7Yrdiz2KfYqCDYtNmF2Kc8L3NwYW4+YH0KICAgICAgICA8L2Rpdj4KICAgICAgPC9kaXY+YCl9YCkuam9pbigiIil9CiAgICA8L2Rpdj4KICA8L2Rpdj5gOwp9CgovKiA9PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT0KICAg2K/Yp9i02KjZiNix2K8g2LHZiNin2KjYtyDYudmF2YjZhduMCiAgID09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PSAqLwpmdW5jdGlvbiBzY3JlZW5QckRhc2hib2FyZCgpIHsKICBjb25zdCBwciA9IHN0YXRlLmFkbWluLnByIHx8IHt9OwogIGNvbnN0IGF2Z3MgPSBwci5hdmVyYWdlcyB8fCB7fTsKICByZXR1cm4gYDxkaXYgY2xhc3M9Im1heC13LTJ4bCBteC1hdXRvIHAtNSBwYi0xMCI+CiAgICAke1RvcEJhcigi2K/Yp9i02KjZiNix2K8g2LHZiNin2KjYtyDYudmF2YjZhduMIiwgImdvU3RhZmZEYXNoYm9hcmQiKX0KICAgICR7Q2FyZChgPGRpdiBjbGFzcz0icC01Ij4KICAgICAgPHAgY2xhc3M9InRleHQteHMgZm9udC1ib2xkIHRleHQtdGVhbC04MDAgbWItNCI+2YXbjNin2Ybar9uM2YYg2LHYttin24zYqiDYp9iyINmH2LEg2YjYp9it2K8gKNin2LIg27UpPC9wPgogICAgICAke1NVUlZFWV9DQVRFR09SSUVTLm1hcCgoW2tleSxsYWJlbF0pID0+IEJhclJvdyhsYWJlbCwgYXZnc1trZXldfHwwLCA1LCAiYW1iZXIiKSkuam9pbigiIil9CiAgICA8L2Rpdj5gLCAibWItNSIpfQogICAgJHtDYXJkKGA8ZGl2IGNsYXNzPSJwLTUiPgogICAgICA8cCBjbGFzcz0idGV4dC14cyBmb250LWJvbGQgdGV4dC10ZWFsLTgwMCBtYi00Ij7Zhtit2YjZh+KAjNuMINii2LTZhtin24zbjCDZhdix2KfYrNi52YfigIzaqdmG2YbYr9qv2KfZhjwvcD4KICAgICAgJHsocHIucmVmZXJyYWxCcmVha2Rvd258fFtdKS5tYXAoKHIpID0+IEJhclJvdyhgJHtyLnNvdXJjZX0gKCR7ZmFEaWdpdHMoci5wZXJjZW50KX0lKWAsIHIuY291bnQsIE1hdGgubWF4KC4uLihwci5yZWZlcnJhbEJyZWFrZG93bnx8W3tjb3VudDoxfV0pLm1hcCh4PT54LmNvdW50KSksICJ0ZWFsIikpLmpvaW4oIiIpfQogICAgPC9kaXY+YCwgIm1iLTUiKX0KICAgICR7Q2FyZChgPGRpdiBjbGFzcz0icC01Ij4KICAgICAgPHAgY2xhc3M9InRleHQteHMgZm9udC1ib2xkIHRleHQtdGVhbC04MDAgbWItNCI+2LHZiNmG2K8g2LHYttin24zYqiDYr9ixINi32YjZhCDYstmF2KfZhjwvcD4KICAgICAgJHsocHIudHJlbmR8fFtdKS5tYXAoKHQpID0+IEJhclJvdyh0Lm1vbnRoLCB0LmF2ZywgNSwgImVtZXJhbGQiKSkuam9pbigiIikgfHwgYDxwIGNsYXNzPSJ0ZXh0LXhzIHRleHQtc3RvbmUtNDAwIj7Yr9in2K/Zh+KAjNuMINqp2KfZgduMINmG24zYs9iqPC9wPmB9CiAgICA8L2Rpdj5gLCAibWItNSIpfQogICAgJHtDYXJkKGA8ZGl2IGNsYXNzPSJwLTUiPgogICAgICA8cCBjbGFzcz0idGV4dC14cyBmb250LWJvbGQgdGV4dC10ZWFsLTgwMCBtYi00Ij7ZvtuM2LTZhtmH2KfYr9mH2Kcg2Ygg2KfZhtiq2YLYp9iv2KfYqjwvcD4KICAgICAgJHsocHIuY29tcGxhaW50c3x8W10pLmxlbmd0aD09PTAgPyBgPHAgY2xhc3M9InRleHQteHMgdGV4dC1zdG9uZS00MDAiPtmF2YjYsdiv24wg2KvYqNiqINmG2LTYr9mHPC9wPmAgOiBwci5jb21wbGFpbnRzLm1hcCgoYykgPT4gYAogICAgICAgIDxkaXYgY2xhc3M9ImJnLXN0b25lLTUwIHJvdW5kZWQtbGcgcC0zIG1iLTIgdGV4dC14cyI+PHAgY2xhc3M9InRleHQtc3RvbmUtNzAwIj4ke2VzYyhjLnRleHQpfTwvcD48cCBjbGFzcz0idGV4dC1zdG9uZS00MDAgbXQtMSI+JHtmbXREYXRlU2hvcnQoYy5kYXRlKX08L3A+PC9kaXY+CiAgICAgIGApLmpvaW4oIiIpfQogICAgPC9kaXY+YCl9CiAgICA8ZGl2IGNsYXNzPSJtdC00IG5vLXByaW50Ij4ke0dob3N0QnV0dG9uKCImIzEyODQyNDsmIzY1MDM5OyDZhtiz2K7Zh+KAjNuMINmC2KfYqNmEINqG2KfZviAoUERGKSIsICJwcmludFJlcG9ydCIpfTwvZGl2PgogIDwvZGl2PmA7Cn0KCi8qID09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PQogICDYr9in2LTYqNmI2LHYryBDUk0KICAgPT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09ICovCmZ1bmN0aW9uIHNjcmVlbkNybURhc2hib2FyZCgpIHsKICBjb25zdCBjID0gc3RhdGUuYWRtaW4uY3JtIHx8IHt9OwogIHJldHVybiBgPGRpdiBjbGFzcz0ibWF4LXctMnhsIG14LWF1dG8gcC01IHBiLTEwIj4KICAgICR7VG9wQmFyKCLYr9in2LTYqNmI2LHYryBDUk0iLCAiZ29TdGFmZkRhc2hib2FyZCIpfQogICAgPGRpdiBjbGFzcz0iZ3JpZCBncmlkLWNvbHMtMiBzbTpncmlkLWNvbHMtNCBnYXAtMyBtYi01Ij4KICAgICAgJHtTdGF0Q2FyZCgiJiMxMjgxMDA7Iiwi2KfZh9iv2KfaqdmG2YbYr9qv2KfZhiDZgdi52KfZhCIsYy5hY3RpdmVEb25vcnMpfQogICAgICAke1N0YXRDYXJkKCImIzEyODY4MzsiLCLYutuM2LHZgdi52KfZhCIsYy5pbmFjdGl2ZURvbm9ycyl9CiAgICAgICR7U3RhdENhcmQoIiYjOTg4ODsmIzY1MDM5OyIsItmG24zYp9iy2YXZhtivINm+24zar9uM2LHbjCIsYy5uZWVkc0ZvbGxvd3VwKX0KICAgICAgJHtTdGF0Q2FyZCgiJiM5MjAwOyIsItuM2KfYr9ii2YjYsdmH2KfbjCDZhdi52YjZgiIsYy5wZW5kaW5nUmVtaW5kZXJzKX0KICAgIDwvZGl2PgogICAgJHtDYXJkKGA8ZGl2IGNsYXNzPSJwLTUiPgogICAgICA8cCBjbGFzcz0idGV4dC14cyBmb250LWJvbGQgdGV4dC10ZWFsLTgwMCBtYi00Ij7Yr9mE2KfbjNmEINin2LXZhNuMINmE2LrZiCDZhtmI2KjYqjwvcD4KICAgICAgJHsoYy5jYW5jZWxSZWFzb25zfHxbXSkubGVuZ3RoPT09MCA/IGA8cCBjbGFzcz0idGV4dC14cyB0ZXh0LXN0b25lLTQwMCI+2YTYutmI24wg2KvYqNiqINmG2LTYr9mHPC9wPmAgOiBjLmNhbmNlbFJlYXNvbnMubWFwKChyKSA9PiBCYXJSb3coci5yZWFzb24sIHIuY291bnQsIE1hdGgubWF4KC4uLmMuY2FuY2VsUmVhc29ucy5tYXAoeD0+eC5jb3VudCkpLCAicm9zZSIpKS5qb2luKCIiKX0KICAgIDwvZGl2PmAsICJtYi01Iil9CiAgICAke0NhcmQoYDxkaXYgY2xhc3M9InAtNSI+CiAgICAgIDxwIGNsYXNzPSJ0ZXh0LXhzIGZvbnQtYm9sZCB0ZXh0LXRlYWwtODAwIG1iLTQiPtmF2YfZheKAjNiq2LHbjNmGINmF2LPbjNix2YfYp9uMINis2LDYqDwvcD4KICAgICAgJHsoYy5yZWZlcnJhbEJyZWFrZG93bnx8W10pLm1hcCgocikgPT4gQmFyUm93KHIuc291cmNlLCByLmNvdW50LCBNYXRoLm1heCguLi4oYy5yZWZlcnJhbEJyZWFrZG93bnx8W3tjb3VudDoxfV0pLm1hcCh4PT54LmNvdW50KSksICJ0ZWFsIikpLmpvaW4oIiIpfQogICAgPC9kaXY+YCwgIm1iLTUiKX0KICAgICR7c3RhdGUuc3RhZmYucm9sZSA9PT0gImFkbWluIiA/IEdob3N0QnV0dG9uKCImIzEyODIyMDsg2YTYp9qvINmB2LnYp9mE24zYqiDaqdin2LHaqdmG2KfZhiIsICJnb0FjdGl2aXR5TG9nIikgOiAiIn0KICA8L2Rpdj5gOwp9CgpmdW5jdGlvbiBzY3JlZW5BY3Rpdml0eUxvZygpIHsKICBjb25zdCBsb2cgPSBzdGF0ZS5hZG1pbi5hY3Rpdml0eUxvZyB8fCBbXTsKICByZXR1cm4gYDxkaXYgY2xhc3M9Im1heC13LTJ4bCBteC1hdXRvIHAtNSBwYi0xMCI+CiAgICAke1RvcEJhcigi2YTYp9qvINmB2LnYp9mE24zYqiDaqdin2LHaqdmG2KfZhiIsICJnb0NybURhc2hib2FyZCIpfQogICAgPGRpdiBjbGFzcz0ic3BhY2UteS0yIj4KICAgICAgJHtsb2cubWFwKChhKSA9PiBgJHtDYXJkKGA8ZGl2IGNsYXNzPSJwLTMgdGV4dC14cyI+PHAgY2xhc3M9InRleHQtc3RvbmUtNzAwIj4ke2VzYyhhLmFjdG9yVXNlcm5hbWUpfSDigJQgJHtlc2MoYS5kZXRhaWwpfTwvcD48cCBjbGFzcz0idGV4dC1zdG9uZS00MDAgbXQtMSI+JHtmbXREYXRlVGltZShhLmNyZWF0ZWRBdCl9PC9wPjwvZGl2PmApfWApLmpvaW4oIiIpfQogICAgPC9kaXY+CiAgPC9kaXY+YDsKfQoKLyogPT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09CiAgINmB2LHZhSDYq9io2Kog2YbYqtuM2KzZh+KAjNuMINmF2LHYp9is2LnZhwogICA9PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT0gKi8KZnVuY3Rpb24gc2NyZWVuT3V0Y29tZUZvcm0oKSB7CiAgY29uc3QgZiA9IHN0YXRlLmZvcm07CiAgcmV0dXJuIGA8ZGl2IGNsYXNzPSJtYXgtdy1zbSBteC1hdXRvIHAtNSI+CiAgICAke1RvcEJhcigi2KvYqNiqINmG2KrbjNis2YfigIzbjCDZhdix2KfYrNi52YciLCAiYmFja1RvRG9ub3JEZXRhaWwiKX0ke0Vycm9yQm94KHN0YXRlLmVycm9yTXNnKX0KICAgICR7Q2FyZChgPGRpdiBjbGFzcz0icC01IHNwYWNlLXktNCI+CiAgICAgIDxsYWJlbCBjbGFzcz0iZmxleCBpdGVtcy1jZW50ZXIgZ2FwLTIgdGV4dC1zbSI+PGlucHV0IHR5cGU9ImNoZWNrYm94IiBkYXRhLWFjdGlvbj0idG9nZ2xlT3V0Y29tZUF0dGVuZGVkIiAke2YuYXR0ZW5kZWQ/ImNoZWNrZWQiOiIifSAvPiDZhdix2KfYrNi52Ycg2qnYsdivPC9sYWJlbD4KICAgICAgPGRpdj4KICAgICAgICA8cCBjbGFzcz0idGV4dC1zbSBmb250LXNlbWlib2xkIHRleHQtdGVhbC05NTAgbWItMiI+2YbYqtuM2KzZhzwvcD4KICAgICAgICA8ZGl2IGNsYXNzPSJncmlkIGdyaWQtY29scy0yIGdhcC0yIj4KICAgICAgICAgIDxidXR0b24gZGF0YS1hY3Rpb249InNldEZvcm0iIGRhdGEta2V5PSJkb25hdGVkIiBkYXRhLXZhbHVlPSJ0cnVlIiBjbGFzcz0icHktMi41IHJvdW5kZWQtbGcgdGV4dC1zbSBib3JkZXIgJHtmLmRvbmF0ZWQ9PT10cnVlPyJiZy1lbWVyYWxkLTYwMCB0ZXh0LXdoaXRlIGJvcmRlci1lbWVyYWxkLTYwMCI6ImJnLXdoaXRlIGJvcmRlci1zdG9uZS0yMDAifSI+2KfZh9iv2Kcg2KfZhtis2KfZhSDYtNivPC9idXR0b24+CiAgICAgICAgICA8YnV0dG9uIGRhdGEtYWN0aW9uPSJzZXRGb3JtIiBkYXRhLWtleT0iZG9uYXRlZCIgZGF0YS12YWx1ZT0iZmFsc2UiIGNsYXNzPSJweS0yLjUgcm91bmRlZC1sZyB0ZXh0LXNtIGJvcmRlciAke2YuZG9uYXRlZD09PWZhbHNlPyJiZy1yb3NlLTYwMCB0ZXh0LXdoaXRlIGJvcmRlci1yb3NlLTYwMCI6ImJnLXdoaXRlIGJvcmRlci1zdG9uZS0yMDAifSI+2KfZh9iv2Kcg2KfZhtis2KfZhSDZhti02K88L2J1dHRvbj4KICAgICAgICA8L2Rpdj4KICAgICAgPC9kaXY+CiAgICAgICR7Zi5kb25hdGVkID09PSBmYWxzZSA/IGA8ZGl2PjxsYWJlbCBjbGFzcz0idGV4dC14cyB0ZXh0LXN0b25lLTUwMCI+2LnZhNiqINi52K/ZhSDYp9mH2K/YpzwvbGFiZWw+PGlucHV0IGlkPSJub3REb25hdGVkUmVhc29uSW5wdXQiIGNsYXNzPSJ3LWZ1bGwgYm9yZGVyIGJvcmRlci1zdG9uZS0yMDAgcm91bmRlZC14bCBweC00IHB5LTMgbXQtMSIgLz48L2Rpdj5gIDogIiJ9CiAgICAgICR7UHJpbWFyeUJ1dHRvbigi2KvYqNiqINmG2KrbjNis2YciLCAic3VibWl0T3V0Y29tZSIpfQogICAgPC9kaXY+YCl9CiAgPC9kaXY+YDsKfQoKLyogPT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09CiAgINiv24zYs9m+2obYsSDYsdmG2K/YsQogICA9PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT0gKi8KZnVuY3Rpb24gcmVuZGVyKCkgewogIGNvbnN0IGFwcCA9IGRvY3VtZW50LmdldEVsZW1lbnRCeUlkKCJhcHAiKTsKICBsZXQgaHRtbDsKICBzd2l0Y2ggKHN0YXRlLnNjcmVlbikgewogICAgY2FzZSAibGFuZGluZyI6IGh0bWwgPSBzY3JlZW5MYW5kaW5nKCk7IGJyZWFrOwogICAgY2FzZSAiZG9ub3JPdHBQaG9uZSI6IGh0bWwgPSBzY3JlZW5Eb25vck90cFBob25lKCk7IGJyZWFrOwogICAgY2FzZSAiZG9ub3JPdHBDb2RlIjogaHRtbCA9IHNjcmVlbkRvbm9yT3RwQ29kZSgpOyBicmVhazsKICAgIGNhc2UgImRvbm9yUmVnaXN0ZXIiOiBodG1sID0gc2NyZWVuRG9ub3JSZWdpc3RlcigpOyBicmVhazsKICAgIGNhc2UgImRvbm9yU3VydmV5IjogaHRtbCA9IHNjcmVlbkRvbm9yU3VydmV5KCk7IGJyZWFrOwogICAgY2FzZSAiZG9ub3JUZXN0UGVuZGluZyI6IGh0bWwgPSBzY3JlZW5Eb25vclRlc3RQZW5kaW5nKCk7IGJyZWFrOwogICAgY2FzZSAiZG9ub3JIb21lIjogaHRtbCA9IHNjcmVlbkRvbm9ySG9tZSgpOyBicmVhazsKICAgIGNhc2UgImRvbm9yQm9vayI6IGh0bWwgPSBzY3JlZW5Eb25vckJvb2soKTsgYnJlYWs7CiAgICBjYXNlICJkb25vckZvbGxvd1VwIjogaHRtbCA9IHNjcmVlbkRvbm9yRm9sbG93VXAoKTsgYnJlYWs7CiAgICBjYXNlICJzdGFmZkxvZ2luIjogaHRtbCA9IHNjcmVlblN0YWZmTG9naW4oKTsgYnJlYWs7CiAgICBjYXNlICJjaGFuZ2VQYXNzd29yZCI6IGh0bWwgPSBzY3JlZW5DaGFuZ2VQYXNzd29yZCgpOyBicmVhazsKICAgIGNhc2UgInN0YWZmRGFzaGJvYXJkIjogaHRtbCA9IHNjcmVlblN0YWZmRGFzaGJvYXJkKCk7IGJyZWFrOwogICAgY2FzZSAibm90aWZDZW50ZXIiOiBodG1sID0gc2NyZWVuTm90aWZDZW50ZXIoKTsgYnJlYWs7CiAgICBjYXNlICJkb25vckxpc3QiOiBodG1sID0gc2NyZWVuRG9ub3JMaXN0KCk7IGJyZWFrOwogICAgY2FzZSAiZG9ub3JEZXRhaWwiOiBodG1sID0gc2NyZWVuRG9ub3JEZXRhaWwoKTsgYnJlYWs7CiAgICBjYXNlICJhcHBvaW50bWVudHMiOiBodG1sID0gc2NyZWVuQXBwb2ludG1lbnRzKCk7IGJyZWFrOwogICAgY2FzZSAic2V0dGluZ3MiOiBodG1sID0gc2NyZWVuU2V0dGluZ3MoKTsgYnJlYWs7CiAgICBjYXNlICJzdGFmZlVzZXJzIjogaHRtbCA9IHNjcmVlblN0YWZmVXNlcnMoKTsgYnJlYWs7CiAgICBjYXNlICJwckRhc2hib2FyZCI6IGh0bWwgPSBzY3JlZW5QckRhc2hib2FyZCgpOyBicmVhazsKICAgIGNhc2UgImNybURhc2hib2FyZCI6IGh0bWwgPSBzY3JlZW5Dcm1EYXNoYm9hcmQoKTsgYnJlYWs7CiAgICBjYXNlICJhY3Rpdml0eUxvZyI6IGh0bWwgPSBzY3JlZW5BY3Rpdml0eUxvZygpOyBicmVhazsKICAgIGNhc2UgIm91dGNvbWVGb3JtIjogaHRtbCA9IHNjcmVlbk91dGNvbWVGb3JtKCk7IGJyZWFrOwogICAgZGVmYXVsdDogaHRtbCA9IHNjcmVlbkxhbmRpbmcoKTsKICB9CiAgYXBwLmlubmVySFRNTCA9IGA8ZGl2IGNsYXNzPSJmYWRlLWluIj4ke2h0bWx9PC9kaXY+YDsKfQoKLyogPT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09CiAgINin2qnYtNmG4oCM2YfYp9uMINin2YfYr9in2qnZhtmG2K/ZhwogICA9PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT0gKi8KZnVuY3Rpb24gZ29Eb25vckF1dGgoKSB7IHNldFNjcmVlbigiZG9ub3JPdHBQaG9uZSIpOyB9Cgphc3luYyBmdW5jdGlvbiByZXF1ZXN0T3RwKCkgewogIGNvbnN0IHBob25lID0gZG9jdW1lbnQuZ2V0RWxlbWVudEJ5SWQoInBob25lSW5wdXQiKS52YWx1ZS5yZXBsYWNlKC9bXjAtOV0vZywgIiIpOwogIGlmIChwaG9uZS5sZW5ndGggPCAxMCkgeyBzdGF0ZS5lcnJvck1zZyA9ICLYtNmF2KfYsdmHINmF2YjYqNin24zZhCDZhdi52KrYqNixINmG24zYs9iqIjsgcmVuZGVyKCk7IHJldHVybjsgfQogIHRyeSB7CiAgICBjb25zdCByZXMgPSBhd2FpdCBhcGkoIlBPU1QiLCAiL2FwaS9kb25vci1hdXRoL3JlcXVlc3Qtb3RwIiwgeyBwaG9uZSB9KTsKICAgIHN0YXRlLmZvcm0gPSB7IHBob25lLCBkZW1vQ29kZTogcmVzLmRlbW9Db2RlIH07CiAgICBzZXRTY3JlZW4oImRvbm9yT3RwQ29kZSIsIGZhbHNlKTsKICB9IGNhdGNoIChlKSB7IHN0YXRlLmVycm9yTXNnID0gZS5tZXNzYWdlOyByZW5kZXIoKTsgfQp9Cgphc3luYyBmdW5jdGlvbiB2ZXJpZnlPdHAoKSB7CiAgY29uc3QgY29kZSA9IGRvY3VtZW50LmdldEVsZW1lbnRCeUlkKCJvdHBJbnB1dCIpLnZhbHVlLnRyaW0oKTsKICB0cnkgewogICAgY29uc3QgcmVzID0gYXdhaXQgYXBpKCJQT1NUIiwgIi9hcGkvZG9ub3ItYXV0aC92ZXJpZnktb3RwIiwgeyBwaG9uZTogc3RhdGUuZm9ybS5waG9uZSwgY29kZSB9KTsKICAgIGlmIChyZXMuZXhpc3RzKSB7CiAgICAgIGF3YWl0IGxvYWREb25vckhvbWUoc3RhdGUuZm9ybS5waG9uZSk7CiAgICB9IGVsc2UgewogICAgICBzdGF0ZS5mb3JtID0geyBwaG9uZTogc3RhdGUuZm9ybS5waG9uZSB9OwogICAgICBzZXRTY3JlZW4oImRvbm9yUmVnaXN0ZXIiLCBmYWxzZSk7CiAgICB9CiAgfSBjYXRjaCAoZSkgeyBzdGF0ZS5lcnJvck1zZyA9IGUubWVzc2FnZTsgcmVuZGVyKCk7IH0KfQoKYXN5bmMgZnVuY3Rpb24gc3VibWl0UmVnaXN0ZXIoKSB7CiAgY29uc3QgZmlyc3ROYW1lID0gZG9jdW1lbnQuZ2V0RWxlbWVudEJ5SWQoImZpcnN0TmFtZUlucHV0IikudmFsdWUudHJpbSgpOwogIGNvbnN0IGxhc3ROYW1lID0gZG9jdW1lbnQuZ2V0RWxlbWVudEJ5SWQoImxhc3ROYW1lSW5wdXQiKS52YWx1ZS50cmltKCk7CiAgY29uc3QgYWdlID0gZG9jdW1lbnQuZ2V0RWxlbWVudEJ5SWQoImFnZUlucHV0IikudmFsdWU7CiAgdHJ5IHsKICAgIGF3YWl0IGFwaSgiUE9TVCIsICIvYXBpL2Rvbm9yLWF1dGgvcmVnaXN0ZXIiLCB7IHBob25lOiBzdGF0ZS5mb3JtLnBob25lLCBmaXJzdE5hbWUsIGxhc3ROYW1lLCBhZ2UgfSk7CiAgICBhd2FpdCBsb2FkRG9ub3JIb21lKHN0YXRlLmZvcm0ucGhvbmUpOwogIH0gY2F0Y2ggKGUpIHsgc3RhdGUuZXJyb3JNc2cgPSBlLm1lc3NhZ2U7IHJlbmRlcigpOyB9Cn0KCmFzeW5jIGZ1bmN0aW9uIGxvYWREb25vckhvbWUocGhvbmUpIHsKICB0cnkgewogICAgY29uc3QgZG9ub3IgPSBhd2FpdCBhcGkoIkdFVCIsIGAvYXBpL2Rvbm9ycy8ke3Bob25lfWApOwogICAgc3RhdGUuZG9ub3IgPSBkb25vcjsKICAgIHN0YXRlLmRvbm9yTm90aWZpY2F0aW9ucyA9IGF3YWl0IGFwaSgiR0VUIiwgYC9hcGkvZG9ub3JzLyR7cGhvbmV9L25vdGlmaWNhdGlvbnNgKTsKICAgIGlmICghZG9ub3Iuc3VydmV5KSBzZXRTY3JlZW4oImRvbm9yU3VydmV5IiwgdHJ1ZSk7CiAgICBlbHNlIGlmICghZG9ub3IubGFiQXBwcm92ZWRBdCkgc2V0U2NyZWVuKCJkb25vclRlc3RQZW5kaW5nIiwgdHJ1ZSk7CiAgICBlbHNlIHNldFNjcmVlbigiZG9ub3JIb21lIiwgdHJ1ZSk7CiAgfSBjYXRjaCAoZSkgeyBzdGF0ZS5lcnJvck1zZyA9IGUubWVzc2FnZTsgcmVuZGVyKCk7IH0KfQoKYXN5bmMgZnVuY3Rpb24gc3VibWl0U3VydmV5KCkgewogIGNvbnN0IGZyZWVUZXh0ID0gZG9jdW1lbnQuZ2V0RWxlbWVudEJ5SWQoImZyZWVUZXh0SW5wdXQiKS52YWx1ZS50cmltKCk7CiAgY29uc3QgcGF5bG9hZCA9IHsgLi4uc3RhdGUuZm9ybSwgZnJlZVRleHQgfTsKICB0cnkgewogICAgYXdhaXQgYXBpKCJQT1NUIiwgYC9hcGkvZG9ub3JzLyR7c3RhdGUuZm9ybS5waG9uZX0vc3VydmV5YCwgcGF5bG9hZCk7CiAgICBhd2FpdCBsb2FkRG9ub3JIb21lKHN0YXRlLmZvcm0ucGhvbmUpOwogIH0gY2F0Y2ggKGUpIHsgc3RhdGUuZXJyb3JNc2cgPSBlLm1lc3NhZ2U7IHJlbmRlcigpOyB9Cn0KCmZ1bmN0aW9uIGRvbm9yTG9nb3V0QWN0aW9uKCkgeyBzdGF0ZS5kb25vciA9IG51bGw7IHN0YXRlLmRvbm9yTm90aWZpY2F0aW9ucyA9IFtdOyBzZXRTY3JlZW4oImxhbmRpbmciKTsgfQoKZnVuY3Rpb24gYmFja1RvRG9ub3JIb21lKCkgeyBzZXRTY3JlZW4oImRvbm9ySG9tZSIpOyB9CgpmdW5jdGlvbiBnb0Jvb2tBcHBvaW50bWVudCgpIHsKICBzdGF0ZS5mb3JtID0geyBib29rRGF0ZTogdG9kYXlJU09EYXRlKCksIGFwcG9pbnRtZW50TW9kZTogImF1dG8iIH07CiAgYXBpKCJHRVQiLCAiL2FwaS9hZG1pbi9zZXR0aW5ncyIpLmNhdGNoKCgpID0+IHt9KTsKICBsb2FkUHVibGljU2V0dGluZ3NGb3JCb29raW5nKCk7Cn0KYXN5bmMgZnVuY3Rpb24gbG9hZFB1YmxpY1NldHRpbmdzRm9yQm9va2luZygpIHsKICB0cnkgewogICAgY29uc3QgZG9ub3IgPSBhd2FpdCBhcGkoIkdFVCIsIGAvYXBpL2Rvbm9ycy8ke3N0YXRlLmRvbm9yLnBob25lfWApOwogICAgc3RhdGUuZG9ub3IgPSBkb25vcjsKICB9IGNhdGNoIChlKSB7fQogIHNldFNjcmVlbigiZG9ub3JCb29rIiwgZmFsc2UpOwp9Cgphc3luYyBmdW5jdGlvbiBsb2FkU2xvdHMoKSB7CiAgY29uc3QgZGF0ZSA9IGRvY3VtZW50LmdldEVsZW1lbnRCeUlkKCJib29rRGF0ZUlucHV0IikudmFsdWU7CiAgc3RhdGUuZm9ybS5ib29rRGF0ZSA9IGRhdGU7CiAgdHJ5IHsKICAgIGNvbnN0IHNsb3RzID0gYXdhaXQgYXBpKCJHRVQiLCBgL2FwaS9kb25vcnMvJHtzdGF0ZS5kb25vci5waG9uZX0vc2xvdHM/ZGF0ZT0ke2RhdGV9YCk7CiAgICBzdGF0ZS5mb3JtLnNsb3RzID0gc2xvdHM7CiAgICByZW5kZXIoKTsKICB9IGNhdGNoIChlKSB7IHN0YXRlLmVycm9yTXNnID0gZS5tZXNzYWdlOyByZW5kZXIoKTsgfQp9CmZ1bmN0aW9uIHBpY2tTbG90KHRpbWUpIHsgc3RhdGUuZm9ybS5waWNrZWRUaW1lID0gdGltZTsgcmVuZGVyKCk7IH0KCmFzeW5jIGZ1bmN0aW9uIHN1Ym1pdEJvb2tpbmcoKSB7CiAgY29uc3QgZGF0ZSA9IGRvY3VtZW50LmdldEVsZW1lbnRCeUlkKCJib29rRGF0ZUlucHV0IikudmFsdWU7CiAgY29uc3QgaXNBdXRvID0gc3RhdGUuZm9ybS5hcHBvaW50bWVudE1vZGUgPT09ICJhdXRvIjsKICBjb25zdCB0aW1lID0gaXNBdXRvID8gc3RhdGUuZm9ybS5waWNrZWRUaW1lIDogKGRvY3VtZW50LmdldEVsZW1lbnRCeUlkKCJib29rVGltZUlucHV0IikgPyBkb2N1bWVudC5nZXRFbGVtZW50QnlJZCgiYm9va1RpbWVJbnB1dCIpLnZhbHVlIDogIiIpOwogIGNvbnN0IG5vdGUgPSBkb2N1bWVudC5nZXRFbGVtZW50QnlJZCgiYm9va05vdGVJbnB1dCIpID8gZG9jdW1lbnQuZ2V0RWxlbWVudEJ5SWQoImJvb2tOb3RlSW5wdXQiKS52YWx1ZSA6ICIiOwogIHRyeSB7CiAgICBjb25zdCBkb25vciA9IGF3YWl0IGFwaSgiUE9TVCIsIGAvYXBpL2Rvbm9ycy8ke3N0YXRlLmRvbm9yLnBob25lfS9hcHBvaW50bWVudHNgLCB7IGRhdGUsIHRpbWUsIG5vdGUgfSk7CiAgICBzdGF0ZS5kb25vciA9IGRvbm9yOwogICAgc2hvd1RvYXN0KCLZhtmI2KjYqiDYq9io2Kog2LTYryIpOwogICAgc2V0U2NyZWVuKCJkb25vckhvbWUiKTsKICB9IGNhdGNoIChlKSB7IHN0YXRlLmVycm9yTXNnID0gZS5tZXNzYWdlOyByZW5kZXIoKTsgfQp9Cgphc3luYyBmdW5jdGlvbiBjYW5jZWxBcHBvaW50bWVudChpZCkgewogIHRyeSB7CiAgICBzdGF0ZS5kb25vciA9IGF3YWl0IGFwaSgiUE9TVCIsIGAvYXBpL2Rvbm9ycy8ke3N0YXRlLmRvbm9yLnBob25lfS9hcHBvaW50bWVudHMvJHtpZH0vY2FuY2VsYCk7CiAgICBzaG93VG9hc3QoItmG2YjYqNiqINmE2LrZiCDYtNivIiwgInJvc2UiKTsKICAgIHJlbmRlcigpOwogIH0gY2F0Y2ggKGUpIHsgc3RhdGUuZXJyb3JNc2cgPSBlLm1lc3NhZ2U7IHJlbmRlcigpOyB9Cn0KYXN5bmMgZnVuY3Rpb24gYWNjZXB0UmVzY2hlZHVsZShpZCkgewogIHRyeSB7CiAgICBzdGF0ZS5kb25vciA9IGF3YWl0IGFwaSgiUE9TVCIsIGAvYXBpL2Rvbm9ycy8ke3N0YXRlLmRvbm9yLnBob25lfS9hcHBvaW50bWVudHMvJHtpZH0vYWNjZXB0LXJlc2NoZWR1bGVgKTsKICAgIHNob3dUb2FzdCgi2LLZhdin2YYg2KzYr9uM2K8g2KrYp9uM24zYryDYtNivIik7CiAgICByZW5kZXIoKTsKICB9IGNhdGNoIChlKSB7IHN0YXRlLmVycm9yTXNnID0gZS5tZXNzYWdlOyByZW5kZXIoKTsgfQp9CgpmdW5jdGlvbiBvcGVuRm9sbG93VXAoYXBwdElkLCBkYXkpIHsKICBzdGF0ZS5mb3JtID0geyBhcHBvaW50bWVudElkOiBhcHB0SWQsIGRheUluZGV4OiBkYXkgfTsKICBzZXRTY3JlZW4oImRvbm9yRm9sbG93VXAiLCBmYWxzZSk7Cn0KYXN5bmMgZnVuY3Rpb24gc3VibWl0Rm9sbG93VXAoKSB7CiAgY29uc3Qgbm90ZXMgPSBkb2N1bWVudC5nZXRFbGVtZW50QnlJZCgiZm9sbG93dXBOb3RlcyIpLnZhbHVlLnRyaW0oKTsKICBjb25zdCB7IGFwcG9pbnRtZW50SWQsIGRheUluZGV4LCAuLi5hbnN3ZXJzIH0gPSBzdGF0ZS5mb3JtOwogIHRyeSB7CiAgICBzdGF0ZS5kb25vciA9IGF3YWl0IGFwaSgiUE9TVCIsIGAvYXBpL2Rvbm9ycy8ke3N0YXRlLmRvbm9yLnBob25lfS9mb2xsb3d1cHMvJHthcHBvaW50bWVudElkfS8ke2RheUluZGV4fWAsIHsgLi4uYW5zd2Vycywgbm90ZXMgfSk7CiAgICBzaG93VG9hc3QoItmF2YXZhtmI2YYg2KfYsiDZvtin2LPYruKAjNmH2KfYqtmI2YYg8J+MvyIpOwogICAgc2V0U2NyZWVuKCJkb25vckhvbWUiKTsKICB9IGNhdGNoIChlKSB7IHN0YXRlLmVycm9yTXNnID0gZS5tZXNzYWdlOyByZW5kZXIoKTsgfQp9CgovKiA9PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT0KICAg2Kfaqdi02YbigIzZh9in24wg2qnYp9ix2qnZhtin2YYKICAgPT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09ICovCmFzeW5jIGZ1bmN0aW9uIGdvU3RhZmZMb2dpbkFjdGlvbigpIHsKICBpZiAoc3RhdGUuc3RhZmYpIGF3YWl0IGdvU3RhZmZEYXNoYm9hcmRBY3Rpb24oKTsKICBlbHNlIHNldFNjcmVlbigic3RhZmZMb2dpbiIpOwp9Cgphc3luYyBmdW5jdGlvbiBzdGFmZkxvZ2luU3VibWl0KCkgewogIGNvbnN0IHVzZXJuYW1lID0gZG9jdW1lbnQuZ2V0RWxlbWVudEJ5SWQoInN0YWZmVXNlcm5hbWUiKS52YWx1ZS50cmltKCk7CiAgY29uc3QgcGFzc3dvcmQgPSBkb2N1bWVudC5nZXRFbGVtZW50QnlJZCgic3RhZmZQYXNzd29yZCIpLnZhbHVlOwogIHRyeSB7CiAgICBjb25zdCBzdGFmZiA9IGF3YWl0IGFwaSgiUE9TVCIsICIvYXBpL3N0YWZmLWF1dGgvbG9naW4iLCB7IHVzZXJuYW1lLCBwYXNzd29yZCB9KTsKICAgIHN0YXRlLnN0YWZmID0gc3RhZmY7CiAgICBpZiAoc3RhZmYubXVzdENoYW5nZVBhc3N3b3JkKSB7IHN0YXRlLmZvcmNlZFB3Q2hhbmdlID0gdHJ1ZTsgc2V0U2NyZWVuKCJjaGFuZ2VQYXNzd29yZCIpOyB9CiAgICBlbHNlIGF3YWl0IGdvU3RhZmZEYXNoYm9hcmRBY3Rpb24oKTsKICB9IGNhdGNoIChlKSB7IHN0YXRlLmVycm9yTXNnID0gZS5tZXNzYWdlOyByZW5kZXIoKTsgfQp9Cgphc3luYyBmdW5jdGlvbiBzdWJtaXRDaGFuZ2VQYXNzd29yZCgpIHsKICBjb25zdCBjdXJyZW50UGFzc3dvcmQgPSBkb2N1bWVudC5nZXRFbGVtZW50QnlJZCgiY3VyUGFzcyIpLnZhbHVlOwogIGNvbnN0IG5ld1Bhc3N3b3JkID0gZG9jdW1lbnQuZ2V0RWxlbWVudEJ5SWQoIm5ld1Bhc3MiKS52YWx1ZTsKICB0cnkgewogICAgYXdhaXQgYXBpKCJQT1NUIiwgIi9hcGkvc3RhZmYtYXV0aC9jaGFuZ2UtcGFzc3dvcmQiLCB7IGN1cnJlbnRQYXNzd29yZCwgbmV3UGFzc3dvcmQgfSk7CiAgICBzaG93VG9hc3QoItix2YXYsiDYudio2YjYsSDYqti624zbjNixINqp2LHYryIpOwogICAgc3RhdGUuZm9yY2VkUHdDaGFuZ2UgPSBmYWxzZTsKICAgIGF3YWl0IGdvU3RhZmZEYXNoYm9hcmRBY3Rpb24oKTsKICB9IGNhdGNoIChlKSB7IHN0YXRlLmVycm9yTXNnID0gZS5tZXNzYWdlOyByZW5kZXIoKTsgfQp9Cgphc3luYyBmdW5jdGlvbiBzdGFmZkxvZ291dEFjdGlvbigpIHsKICB0cnkgeyBhd2FpdCBhcGkoIlBPU1QiLCAiL2FwaS9zdGFmZi1hdXRoL2xvZ291dCIpOyB9IGNhdGNoIChlKSB7fQogIHN0YXRlLnN0YWZmID0gbnVsbDsKICBzZXRTY3JlZW4oImxhbmRpbmciKTsKfQoKYXN5bmMgZnVuY3Rpb24gZ29TdGFmZkRhc2hib2FyZEFjdGlvbigpIHsKICB0cnkgewogICAgc3RhdGUuYWRtaW4uc3RhdHMgPSBhd2FpdCBhcGkoIkdFVCIsICIvYXBpL2FkbWluL2Rhc2hib2FyZC9zdGF0cyIpOwogICAgc3RhdGUuYWRtaW4ubm90aWZDZW50ZXIgPSBhd2FpdCBhcGkoIkdFVCIsICIvYXBpL2FkbWluL25vdGlmaWNhdGlvbnMtY2VudGVyIik7CiAgICBzZXRTY3JlZW4oInN0YWZmRGFzaGJvYXJkIik7CiAgfSBjYXRjaCAoZSkgeyBzdGF0ZS5zdGFmZiA9IG51bGw7IHN0YXRlLmVycm9yTXNnID0gZS5tZXNzYWdlOyBzZXRTY3JlZW4oInN0YWZmTG9naW4iKTsgfQp9Cgphc3luYyBmdW5jdGlvbiBnb05vdGlmQ2VudGVyKCkgewogIHN0YXRlLmFkbWluLm5vdGlmQ2VudGVyID0gYXdhaXQgYXBpKCJHRVQiLCAiL2FwaS9hZG1pbi9ub3RpZmljYXRpb25zLWNlbnRlciIpOwogIHNldFNjcmVlbigibm90aWZDZW50ZXIiKTsKfQoKYXN5bmMgZnVuY3Rpb24gZ29Eb25vckxpc3QoKSB7CiAgc3RhdGUuYWRtaW4uZG9ub3JzID0gYXdhaXQgYXBpKCJHRVQiLCAiL2FwaS9hZG1pbi9kb25vcnMiKTsKICBzZXRTY3JlZW4oImRvbm9yTGlzdCIpOwp9CmFzeW5jIGZ1bmN0aW9uIHNlYXJjaERvbm9ycygpIHsKICBzdGF0ZS5hZG1pbi5xID0gZG9jdW1lbnQuZ2V0RWxlbWVudEJ5SWQoInNlYXJjaElucHV0IikudmFsdWU7CiAgc3RhdGUuYWRtaW4uZG9ub3JzID0gYXdhaXQgYXBpKCJHRVQiLCBgL2FwaS9hZG1pbi9kb25vcnM/cT0ke2VuY29kZVVSSUNvbXBvbmVudChzdGF0ZS5hZG1pbi5xKX1gKTsKICByZW5kZXIoKTsKfQpmdW5jdGlvbiBleHBvcnRDc3YoKSB7IHdpbmRvdy5vcGVuKCIvYXBpL2FkbWluL2V4cG9ydC9kb25vcnMuY3N2IiwgIl9ibGFuayIpOyB9Cgphc3luYyBmdW5jdGlvbiBvcGVuRG9ub3JCeVBob25lKHBob25lKSB7CiAgdHJ5IHsKICAgIHN0YXRlLmFkbWluLnNlbGVjdGVkRG9ub3IgPSBhd2FpdCBhcGkoIkdFVCIsIGAvYXBpL2FkbWluL2Rvbm9ycy8ke3Bob25lfWApOwogICAgc2V0U2NyZWVuKCJkb25vckRldGFpbCIpOwogIH0gY2F0Y2ggKGUpIHsgc3RhdGUuZXJyb3JNc2cgPSBlLm1lc3NhZ2U7IHJlbmRlcigpOyB9Cn0KYXN5bmMgZnVuY3Rpb24gcmVmcmVzaFNlbGVjdGVkRG9ub3IoKSB7CiAgc3RhdGUuYWRtaW4uc2VsZWN0ZWREb25vciA9IGF3YWl0IGFwaSgiR0VUIiwgYC9hcGkvYWRtaW4vZG9ub3JzLyR7c3RhdGUuYWRtaW4uc2VsZWN0ZWREb25vci5waG9uZX1gKTsKICByZW5kZXIoKTsKfQpmdW5jdGlvbiBiYWNrVG9Eb25vckRldGFpbCgpIHsgc2V0U2NyZWVuKCJkb25vckRldGFpbCIpOyB9Cgphc3luYyBmdW5jdGlvbiBjaGFuZ2VTdGF0dXNBY3Rpb24oc3RhdHVzKSB7CiAgdHJ5IHsgYXdhaXQgYXBpKCJQVVQiLCBgL2FwaS9hZG1pbi9kb25vcnMvJHtzdGF0ZS5hZG1pbi5zZWxlY3RlZERvbm9yLnBob25lfS9zdGF0dXNgLCB7IHN0YXR1cyB9KTsgYXdhaXQgcmVmcmVzaFNlbGVjdGVkRG9ub3IoKTsgc2hvd1RvYXN0KCLZiNi22LnbjNiqINio2LHZiNiy2LHYs9in2YbbjCDYtNivIik7IH0KICBjYXRjaCAoZSkgeyBzdGF0ZS5lcnJvck1zZyA9IGUubWVzc2FnZTsgcmVuZGVyKCk7IH0KfQphc3luYyBmdW5jdGlvbiBhcHByb3ZlTGFiKCkgewogIHRyeSB7IGF3YWl0IGFwaSgiUE9TVCIsIGAvYXBpL2FkbWluL2Rvbm9ycy8ke3N0YXRlLmFkbWluLnNlbGVjdGVkRG9ub3IucGhvbmV9L2FwcHJvdmUtbGFiYCk7IGF3YWl0IHJlZnJlc2hTZWxlY3RlZERvbm9yKCk7IHNob3dUb2FzdCgi2YbYqtuM2KzZhyDYqtin24zbjNivINi02K8g2Ygg2b7bjNin2YXaqSDYp9ix2LPYp9mEINi02K8iKTsgfQogIGNhdGNoIChlKSB7IHN0YXRlLmVycm9yTXNnID0gZS5tZXNzYWdlOyByZW5kZXIoKTsgfQp9CmFzeW5jIGZ1bmN0aW9uIGJsb2NrRG9ub3IoKSB7CiAgdHJ5IHsgYXdhaXQgYXBpKCJQT1NUIiwgYC9hcGkvYWRtaW4vZG9ub3JzLyR7c3RhdGUuYWRtaW4uc2VsZWN0ZWREb25vci5waG9uZX0vYmxvY2tgKTsgYXdhaXQgcmVmcmVzaFNlbGVjdGVkRG9ub3IoKTsgc2hvd1RvYXN0KCLZhdiz2K/ZiNivINi02K8iLCAicm9zZSIpOyB9CiAgY2F0Y2ggKGUpIHsgc3RhdGUuZXJyb3JNc2cgPSBlLm1lc3NhZ2U7IHJlbmRlcigpOyB9Cn0KCmFzeW5jIGZ1bmN0aW9uIGFkZE5vdGUoKSB7CiAgY29uc3QgYm9keSA9IGRvY3VtZW50LmdldEVsZW1lbnRCeUlkKCJub3RlSW5wdXQiKS52YWx1ZS50cmltKCk7CiAgaWYgKCFib2R5KSByZXR1cm47CiAgdHJ5IHsgYXdhaXQgYXBpKCJQT1NUIiwgYC9hcGkvYWRtaW4vZG9ub3JzLyR7c3RhdGUuYWRtaW4uc2VsZWN0ZWREb25vci5waG9uZX0vbm90ZXNgLCB7IGJvZHkgfSk7IGF3YWl0IHJlZnJlc2hTZWxlY3RlZERvbm9yKCk7IH0KICBjYXRjaCAoZSkgeyBzdGF0ZS5lcnJvck1zZyA9IGUubWVzc2FnZTsgcmVuZGVyKCk7IH0KfQphc3luYyBmdW5jdGlvbiBkZWxldGVOb3RlKGlkKSB7CiAgdHJ5IHsgYXdhaXQgYXBpKCJERUxFVEUiLCBgL2FwaS9hZG1pbi9kb25vcnMvJHtzdGF0ZS5hZG1pbi5zZWxlY3RlZERvbm9yLnBob25lfS9ub3Rlcy8ke2lkfWApOyBhd2FpdCByZWZyZXNoU2VsZWN0ZWREb25vcigpOyB9CiAgY2F0Y2ggKGUpIHsgc3RhdGUuZXJyb3JNc2cgPSBlLm1lc3NhZ2U7IHJlbmRlcigpOyB9Cn0KCmFzeW5jIGZ1bmN0aW9uIGFkZFJlbWluZGVyKCkgewogIGNvbnN0IHR5cGUgPSBkb2N1bWVudC5nZXRFbGVtZW50QnlJZCgicmVtaW5kZXJUeXBlIikudmFsdWU7CiAgY29uc3QgZHVlRGF0ZSA9IGRvY3VtZW50LmdldEVsZW1lbnRCeUlkKCJyZW1pbmRlckRhdGUiKS52YWx1ZTsKICBjb25zdCBub3RlID0gZG9jdW1lbnQuZ2V0RWxlbWVudEJ5SWQoInJlbWluZGVyTm90ZSIpLnZhbHVlLnRyaW0oKTsKICBpZiAoIWR1ZURhdGUpIHsgc3RhdGUuZXJyb3JNc2cgPSAi2KrYp9ix24zYriDbjNin2K/YotmI2LEg2LHZiCDYp9mG2KrYrtin2Kgg2qnZhtuM2K8iOyByZW5kZXIoKTsgcmV0dXJuOyB9CiAgdHJ5IHsgYXdhaXQgYXBpKCJQT1NUIiwgYC9hcGkvYWRtaW4vZG9ub3JzLyR7c3RhdGUuYWRtaW4uc2VsZWN0ZWREb25vci5waG9uZX0vcmVtaW5kZXJzYCwgeyB0eXBlLCBkdWVEYXRlOiBuZXcgRGF0ZShkdWVEYXRlKS50b0lTT1N0cmluZygpLCBub3RlIH0pOyBhd2FpdCByZWZyZXNoU2VsZWN0ZWREb25vcigpOyBzaG93VG9hc3QoItuM2KfYr9ii2YjYsSDYq9io2Kog2LTYryIpOyB9CiAgY2F0Y2ggKGUpIHsgc3RhdGUuZXJyb3JNc2cgPSBlLm1lc3NhZ2U7IHJlbmRlcigpOyB9Cn0KYXN5bmMgZnVuY3Rpb24gbWFya1JlbWluZGVyRG9uZShpZCkgewogIHRyeSB7IGF3YWl0IGFwaSgiUE9TVCIsIGAvYXBpL2FkbWluL2Rvbm9ycy8ke3N0YXRlLmFkbWluLnNlbGVjdGVkRG9ub3IucGhvbmV9L3JlbWluZGVycy8ke2lkfS9kb25lYCk7IGF3YWl0IHJlZnJlc2hTZWxlY3RlZERvbm9yKCk7IH0KICBjYXRjaCAoZSkgeyBzdGF0ZS5lcnJvck1zZyA9IGUubWVzc2FnZTsgcmVuZGVyKCk7IH0KfQoKYXN5bmMgZnVuY3Rpb24gY29uZmlybUFwcG9pbnRtZW50KGlkKSB7CiAgdHJ5IHsgYXdhaXQgYXBpKCJQT1NUIiwgYC9hcGkvYWRtaW4vZG9ub3JzLyR7c3RhdGUuYWRtaW4uc2VsZWN0ZWREb25vci5waG9uZX0vYXBwb2ludG1lbnRzLyR7aWR9L2NvbmZpcm1gLCB7fSk7IGF3YWl0IHJlZnJlc2hTZWxlY3RlZERvbm9yKCk7IHNob3dUb2FzdCgi2YbZiNio2Kog2KrYp9uM24zYryDZiCDZvtuM2KfZhdqpINin2LHYs9in2YQg2LTYryIpOyB9CiAgY2F0Y2ggKGUpIHsgc3RhdGUuZXJyb3JNc2cgPSBlLm1lc3NhZ2U7IHJlbmRlcigpOyB9Cn0KYXN5bmMgZnVuY3Rpb24gcHJvcG9zZVJlc2NoZWR1bGUoaWQpIHsKICBjb25zdCBkYXRlID0gcHJvbXB0KCLYqtin2LHbjNiuINmIINiz2KfYudiqINm+24zYtNmG2YfYp9iv24wg2LHYpyDZiNin2LHYryDaqdmG24zYryAo2YXYq9in2YQ6IDIwMjYtMDgtMDFUMTA6MDApIik7CiAgaWYgKCFkYXRlKSByZXR1cm47CiAgdHJ5IHsgYXdhaXQgYXBpKCJQT1NUIiwgYC9hcGkvYWRtaW4vZG9ub3JzLyR7c3RhdGUuYWRtaW4uc2VsZWN0ZWREb25vci5waG9uZX0vYXBwb2ludG1lbnRzLyR7aWR9L3Byb3Bvc2VgLCB7IGRhdGUgfSk7IGF3YWl0IHJlZnJlc2hTZWxlY3RlZERvbm9yKCk7IHNob3dUb2FzdCgi2LLZhdin2YYg2b7bjNi02YbZh9in2K/bjCDYq9io2Kog2LTYryIpOyB9CiAgY2F0Y2ggKGUpIHsgc3RhdGUuZXJyb3JNc2cgPSBlLm1lc3NhZ2U7IHJlbmRlcigpOyB9Cn0KYXN5bmMgZnVuY3Rpb24gY2FuY2VsQXBwdEFkbWluKGlkKSB7CiAgdHJ5IHsgYXdhaXQgYXBpKCJQT1NUIiwgYC9hcGkvYWRtaW4vZG9ub3JzLyR7c3RhdGUuYWRtaW4uc2VsZWN0ZWREb25vci5waG9uZX0vYXBwb2ludG1lbnRzLyR7aWR9L2NhbmNlbGAsIHt9KTsgYXdhaXQgcmVmcmVzaFNlbGVjdGVkRG9ub3IoKTsgc2hvd1RvYXN0KCLZhtmI2KjYqiDZhNi62Ygg2LTYryIsICJyb3NlIik7IH0KICBjYXRjaCAoZSkgeyBzdGF0ZS5lcnJvck1zZyA9IGUubWVzc2FnZTsgcmVuZGVyKCk7IH0KfQpmdW5jdGlvbiBvcGVuT3V0Y29tZUZvcm0oaWQpIHsgc3RhdGUuZm9ybSA9IHsgYXBwdElkOiBpZCwgYXR0ZW5kZWQ6IHRydWUsIGRvbmF0ZWQ6IG51bGwgfTsgc2V0U2NyZWVuKCJvdXRjb21lRm9ybSIsIGZhbHNlKTsgfQpmdW5jdGlvbiB0b2dnbGVPdXRjb21lQXR0ZW5kZWQoKSB7IHN0YXRlLmZvcm0uYXR0ZW5kZWQgPSAhc3RhdGUuZm9ybS5hdHRlbmRlZDsgcmVuZGVyKCk7IH0KYXN5bmMgZnVuY3Rpb24gc3VibWl0T3V0Y29tZSgpIHsKICBjb25zdCBub3REb25hdGVkUmVhc29uID0gZG9jdW1lbnQuZ2V0RWxlbWVudEJ5SWQoIm5vdERvbmF0ZWRSZWFzb25JbnB1dCIpID8gZG9jdW1lbnQuZ2V0RWxlbWVudEJ5SWQoIm5vdERvbmF0ZWRSZWFzb25JbnB1dCIpLnZhbHVlIDogIiI7CiAgdHJ5IHsKICAgIGF3YWl0IGFwaSgiUE9TVCIsIGAvYXBpL2FkbWluL2Rvbm9ycy8ke3N0YXRlLmFkbWluLnNlbGVjdGVkRG9ub3IucGhvbmV9L2FwcG9pbnRtZW50cy8ke3N0YXRlLmZvcm0uYXBwdElkfS9vdXRjb21lYCwgeyBhdHRlbmRlZDogc3RhdGUuZm9ybS5hdHRlbmRlZCwgZG9uYXRlZDogc3RhdGUuZm9ybS5kb25hdGVkLCBub3REb25hdGVkUmVhc29uIH0pOwogICAgYXdhaXQgcmVmcmVzaFNlbGVjdGVkRG9ub3IoKTsKICAgIHNob3dUb2FzdCgi2YbYqtuM2KzZhyDYq9io2Kog2LTYryIpOwogICAgc2V0U2NyZWVuKCJkb25vckRldGFpbCIpOwogIH0gY2F0Y2ggKGUpIHsgc3RhdGUuZXJyb3JNc2cgPSBlLm1lc3NhZ2U7IHJlbmRlcigpOyB9Cn0KYXN5bmMgZnVuY3Rpb24gY3JlYXRlQXBwdEZvckRvbm9yKCkgewogIGNvbnN0IGRhdGUgPSBkb2N1bWVudC5nZXRFbGVtZW50QnlJZCgiYXBwdERhdGUiKS52YWx1ZTsKICBjb25zdCB0aW1lID0gZG9jdW1lbnQuZ2V0RWxlbWVudEJ5SWQoImFwcHRUaW1lIikudmFsdWUgfHwgIjA5OjAwIjsKICBpZiAoIWRhdGUpIHsgc3RhdGUuZXJyb3JNc2cgPSAi2KrYp9ix24zYriDYsdmIINin2YbYqtiu2KfYqCDaqdmG24zYryI7IHJlbmRlcigpOyByZXR1cm47IH0KICB0cnkgewogICAgYXdhaXQgYXBpKCJQT1NUIiwgYC9hcGkvYWRtaW4vZG9ub3JzLyR7c3RhdGUuYWRtaW4uc2VsZWN0ZWREb25vci5waG9uZX0vYXBwb2ludG1lbnRzYCwgeyBkYXRlLCB0aW1lIH0pOwogICAgYXdhaXQgcmVmcmVzaFNlbGVjdGVkRG9ub3IoKTsKICAgIHNob3dUb2FzdCgi2YbZiNio2Kog2KvYqNiqINmIINiq2KfbjNuM2K8g2LTYryIpOwogIH0gY2F0Y2ggKGUpIHsgc3RhdGUuZXJyb3JNc2cgPSBlLm1lc3NhZ2U7IHJlbmRlcigpOyB9Cn0KCmFzeW5jIGZ1bmN0aW9uIGdvQXBwb2ludG1lbnRzKCkgewogIHN0YXRlLmFkbWluLmFwcG9pbnRtZW50cyA9IGF3YWl0IGFwaSgiR0VUIiwgIi9hcGkvYWRtaW4vYXBwb2ludG1lbnRzIik7CiAgc3RhdGUuYWRtaW4uc2xvdERhdGUgPSB0b2RheUlTT0RhdGUoKTsKICBzZXRTY3JlZW4oImFwcG9pbnRtZW50cyIpOwp9CmFzeW5jIGZ1bmN0aW9uIGxvYWRBZG1pblNsb3RzKCkgewogIGNvbnN0IGRhdGUgPSBkb2N1bWVudC5nZXRFbGVtZW50QnlJZCgic2xvdERhdGVJbnB1dCIpLnZhbHVlOwogIHN0YXRlLmFkbWluLnNsb3REYXRlID0gZGF0ZTsKICBzdGF0ZS5hZG1pbi5zbG90cyA9IGF3YWl0IGFwaSgiR0VUIiwgYC9hcGkvYWRtaW4vYXBwb2ludG1lbnRzL3Nsb3RzP2RhdGU9JHtkYXRlfWApOwogIHJlbmRlcigpOwp9Cgphc3luYyBmdW5jdGlvbiBnb1NldHRpbmdzKCkgewogIHN0YXRlLmFkbWluLnNldHRpbmdzID0gYXdhaXQgYXBpKCJHRVQiLCAiL2FwaS9hZG1pbi9zZXR0aW5ncyIpOwogIHNldFNjcmVlbigic2V0dGluZ3MiKTsKfQpmdW5jdGlvbiB0b2dnbGVDbG9zZWREYXkoZGF5KSB7CiAgY29uc3QgcyA9IHN0YXRlLmFkbWluLnNldHRpbmdzOwogIGNvbnN0IGlkeCA9IHMuY2xvc2VkV2Vla2RheXMuaW5kZXhPZihkYXkpOwogIGlmIChpZHggPj0gMCkgcy5jbG9zZWRXZWVrZGF5cy5zcGxpY2UoaWR4LCAxKTsgZWxzZSBzLmNsb3NlZFdlZWtkYXlzLnB1c2goZGF5KTsKICByZW5kZXIoKTsKfQpmdW5jdGlvbiBzZXRBcHBvaW50bWVudE1vZGUobW9kZSkgeyBzdGF0ZS5hZG1pbi5zZXR0aW5ncy5hcHBvaW50bWVudE1vZGUgPSBtb2RlOyByZW5kZXIoKTsgfQphc3luYyBmdW5jdGlvbiBzYXZlU2V0dGluZ3MoKSB7CiAgY29uc3QgcGF5bG9hZCA9IHsKICAgIGNlbnRlck5hbWU6IGRvY3VtZW50LmdldEVsZW1lbnRCeUlkKCJzZXRDZW50ZXJOYW1lIikudmFsdWUudHJpbSgpLAogICAgbWluR2FwSG91cnM6IE51bWJlcihkb2N1bWVudC5nZXRFbGVtZW50QnlJZCgic2V0R2FwRGF5cyIpLnZhbHVlKSAqIDI0LAogICAgZm9sbG93VXBEYXlzOiBOdW1iZXIoZG9jdW1lbnQuZ2V0RWxlbWVudEJ5SWQoInNldEZvbGxvd0RheXMiKS52YWx1ZSksCiAgICBmb2xsb3dVcEZyZXF1ZW5jeVBlckRheTogTnVtYmVyKGRvY3VtZW50LmdldEVsZW1lbnRCeUlkKCJzZXRGb2xsb3dGcmVxIikudmFsdWUpLAogICAgcmVjZXB0aW9uU3RhcnRIb3VyOiBkb2N1bWVudC5nZXRFbGVtZW50QnlJZCgic2V0U3RhcnRIb3VyIikudmFsdWUsCiAgICByZWNlcHRpb25FbmRIb3VyOiBkb2N1bWVudC5nZXRFbGVtZW50QnlJZCgic2V0RW5kSG91ciIpLnZhbHVlLAogICAgY2xvc2VkV2Vla2RheXM6IHN0YXRlLmFkbWluLnNldHRpbmdzLmNsb3NlZFdlZWtkYXlzLAogICAgaG9saWRheXM6IGRvY3VtZW50LmdldEVsZW1lbnRCeUlkKCJzZXRIb2xpZGF5cyIpLnZhbHVlLnNwbGl0KCJcbiIpLm1hcCgocykgPT4gcy50cmltKCkpLmZpbHRlcihCb29sZWFuKSwKICAgIGFwcG9pbnRtZW50TW9kZTogc3RhdGUuYWRtaW4uc2V0dGluZ3MuYXBwb2ludG1lbnRNb2RlLAogICAgaG91cmx5Q2FwYWNpdHk6IE51bWJlcihkb2N1bWVudC5nZXRFbGVtZW50QnlJZCgic2V0Q2FwYWNpdHkiKS52YWx1ZSksCiAgICBub1Nob3dBbGVydERheXM6IE51bWJlcihkb2N1bWVudC5nZXRFbGVtZW50QnlJZCgic2V0Tm9TaG93IikudmFsdWUpLAogIH07CiAgdHJ5IHsgc3RhdGUuYWRtaW4uc2V0dGluZ3MgPSBhd2FpdCBhcGkoIlBVVCIsICIvYXBpL2FkbWluL3NldHRpbmdzIiwgcGF5bG9hZCk7IHNob3dUb2FzdCgi2KrZhti424zZhdin2Kog2LDYrtuM2LHZhyDYtNivIik7IHJlbmRlcigpOyB9CiAgY2F0Y2ggKGUpIHsgc3RhdGUuZXJyb3JNc2cgPSBlLm1lc3NhZ2U7IHJlbmRlcigpOyB9Cn0KYXN5bmMgZnVuY3Rpb24gc2F2ZVNtc1RlbXBsYXRlcygpIHsKICBjb25zdCBrZXlzID0gWyJyZWdpc3RyYXRpb24iLCJwYW5lbEFjdGl2YXRlZCIsImFwcG9pbnRtZW50Q29uZmlybWVkIiwiYXBwb2ludG1lbnRSZW1pbmRlciIsInBvc3REb25hdGlvbkZvbGxvd3VwIiwicmVib29raW5nRW5hYmxlZCJdOwogIGNvbnN0IHBheWxvYWQgPSB7fTsKICBrZXlzLmZvckVhY2goKGspID0+IHsgcGF5bG9hZFtrXSA9IGRvY3VtZW50LmdldEVsZW1lbnRCeUlkKCJ0cGxfIiArIGspLnZhbHVlOyB9KTsKICB0cnkgeyBhd2FpdCBhcGkoIlBVVCIsICIvYXBpL2FkbWluL3NldHRpbmdzL3Ntcy10ZW1wbGF0ZXMiLCBwYXlsb2FkKTsgc2hvd1RvYXN0KCLZhdiq2YYg2b7bjNin2YXaqeKAjNmH2Kcg2LDYrtuM2LHZhyDYtNivIik7IH0KICBjYXRjaCAoZSkgeyBzdGF0ZS5lcnJvck1zZyA9IGUubWVzc2FnZTsgcmVuZGVyKCk7IH0KfQoKYXN5bmMgZnVuY3Rpb24gZ29TdGFmZlVzZXJzKCkgewogIHN0YXRlLmFkbWluLnN0YWZmTGlzdCA9IGF3YWl0IGFwaSgiR0VUIiwgIi9hcGkvYWRtaW4vc3RhZmYiKTsKICBzZXRTY3JlZW4oInN0YWZmVXNlcnMiKTsKfQphc3luYyBmdW5jdGlvbiBhZGRTdGFmZlVzZXIoKSB7CiAgY29uc3QgdXNlcm5hbWUgPSBkb2N1bWVudC5nZXRFbGVtZW50QnlJZCgibmV3U3RhZmZVc2VybmFtZSIpLnZhbHVlLnRyaW0oKTsKICBjb25zdCBwYXNzd29yZCA9IGRvY3VtZW50LmdldEVsZW1lbnRCeUlkKCJuZXdTdGFmZlBhc3N3b3JkIikudmFsdWU7CiAgY29uc3Qgcm9sZSA9IGRvY3VtZW50LmdldEVsZW1lbnRCeUlkKCJuZXdTdGFmZlJvbGUiKS52YWx1ZTsKICB0cnkgeyBhd2FpdCBhcGkoIlBPU1QiLCAiL2FwaS9hZG1pbi9zdGFmZiIsIHsgdXNlcm5hbWUsIHBhc3N3b3JkLCByb2xlIH0pOyBzdGF0ZS5hZG1pbi5zdGFmZkxpc3QgPSBhd2FpdCBhcGkoIkdFVCIsICIvYXBpL2FkbWluL3N0YWZmIik7IHNob3dUb2FzdCgi2qnYp9ix2YXZhtivINin2LbYp9mB2Ycg2LTYryIpOyByZW5kZXIoKTsgfQogIGNhdGNoIChlKSB7IHN0YXRlLmVycm9yTXNnID0gZS5tZXNzYWdlOyByZW5kZXIoKTsgfQp9CmFzeW5jIGZ1bmN0aW9uIHRvZ2dsZUJsb2NrU3RhZmYoaWQsIGJsb2NrZWQpIHsKICB0cnkgeyBhd2FpdCBhcGkoIlBVVCIsIGAvYXBpL2FkbWluL3N0YWZmLyR7aWR9L2Jsb2NrYCwgeyBibG9ja2VkIH0pOyBzdGF0ZS5hZG1pbi5zdGFmZkxpc3QgPSBhd2FpdCBhcGkoIkdFVCIsICIvYXBpL2FkbWluL3N0YWZmIik7IHJlbmRlcigpOyB9CiAgY2F0Y2ggKGUpIHsgc3RhdGUuZXJyb3JNc2cgPSBlLm1lc3NhZ2U7IHJlbmRlcigpOyB9Cn0KYXN5bmMgZnVuY3Rpb24gZGVsZXRlU3RhZmZVc2VyKGlkKSB7CiAgdHJ5IHsgYXdhaXQgYXBpKCJERUxFVEUiLCBgL2FwaS9hZG1pbi9zdGFmZi8ke2lkfWApOyBzdGF0ZS5hZG1pbi5zdGFmZkxpc3QgPSBzdGF0ZS5hZG1pbi5zdGFmZkxpc3QuZmlsdGVyKCh1KSA9PiB1LmlkICE9PSBOdW1iZXIoaWQpKTsgcmVuZGVyKCk7IH0KICBjYXRjaCAoZSkgeyBzdGF0ZS5lcnJvck1zZyA9IGUubWVzc2FnZTsgcmVuZGVyKCk7IH0KfQoKYXN5bmMgZnVuY3Rpb24gZ29QckRhc2hib2FyZCgpIHsgc3RhdGUuYWRtaW4ucHIgPSBhd2FpdCBhcGkoIkdFVCIsICIvYXBpL2FkbWluL2Rhc2hib2FyZC9wciIpOyBzZXRTY3JlZW4oInByRGFzaGJvYXJkIik7IH0KYXN5bmMgZnVuY3Rpb24gZ29Dcm1EYXNoYm9hcmQoKSB7IHN0YXRlLmFkbWluLmNybSA9IGF3YWl0IGFwaSgiR0VUIiwgIi9hcGkvYWRtaW4vZGFzaGJvYXJkL2NybSIpOyBzZXRTY3JlZW4oImNybURhc2hib2FyZCIpOyB9CmFzeW5jIGZ1bmN0aW9uIGdvQWN0aXZpdHlMb2coKSB7IHN0YXRlLmFkbWluLmFjdGl2aXR5TG9nID0gYXdhaXQgYXBpKCJHRVQiLCAiL2FwaS9hZG1pbi9hY3Rpdml0eS1sb2ciKTsgc2V0U2NyZWVuKCJhY3Rpdml0eUxvZyIpOyB9CmZ1bmN0aW9uIHByaW50UmVwb3J0KCkgeyB3aW5kb3cucHJpbnQoKTsgfQoKLyogPT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09CiAgINiv24zYs9m+2obYsSDaqdmE24zaqQogICA9PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT0gKi8KZnVuY3Rpb24gYWN0aW9uU2V0Rm9ybShrZXksIHZhbHVlKSB7CiAgbGV0IHYgPSB2YWx1ZTsKICBpZiAodiA9PT0gInRydWUiKSB2ID0gdHJ1ZTsgZWxzZSBpZiAodiA9PT0gImZhbHNlIikgdiA9IGZhbHNlOwogIGVsc2UgaWYgKC9eWzEtNV0kLy50ZXN0KHZhbHVlKSkgdiA9IE51bWJlcih2YWx1ZSk7CiAgc3RhdGUuZm9ybVtrZXldID0gdjsKICByZW5kZXIoKTsKfQoKZG9jdW1lbnQuYWRkRXZlbnRMaXN0ZW5lcigiY2xpY2siLCBhc3luYyAoZSkgPT4gewogIGNvbnN0IGJ0biA9IGUudGFyZ2V0LmNsb3Nlc3QoIltkYXRhLWFjdGlvbl0iKTsKICBpZiAoIWJ0biB8fCBidG4uZGlzYWJsZWQpIHJldHVybjsKICBjb25zdCBhY3Rpb24gPSBidG4uZGF0YXNldC5hY3Rpb247CiAgY29uc3QgZGF0YSA9IGJ0bi5kYXRhc2V0OwogIHRyeSB7CiAgICBzd2l0Y2ggKGFjdGlvbikgewogICAgICBjYXNlICJnb0xhbmRpbmciOiBzZXRTY3JlZW4oImxhbmRpbmciKTsgYnJlYWs7CiAgICAgIGNhc2UgImdvRG9ub3JBdXRoIjogZ29Eb25vckF1dGgoKTsgYnJlYWs7CiAgICAgIGNhc2UgImdvU3RhZmZMb2dpbiI6IGF3YWl0IGdvU3RhZmZMb2dpbkFjdGlvbigpOyBicmVhazsKICAgICAgY2FzZSAicmVxdWVzdE90cCI6IGF3YWl0IHJlcXVlc3RPdHAoKTsgYnJlYWs7CiAgICAgIGNhc2UgInZlcmlmeU90cCI6IGF3YWl0IHZlcmlmeU90cCgpOyBicmVhazsKICAgICAgY2FzZSAic3VibWl0UmVnaXN0ZXIiOiBhd2FpdCBzdWJtaXRSZWdpc3RlcigpOyBicmVhazsKICAgICAgY2FzZSAic3VibWl0U3VydmV5IjogYXdhaXQgc3VibWl0U3VydmV5KCk7IGJyZWFrOwogICAgICBjYXNlICJkb25vckxvZ291dCI6IGRvbm9yTG9nb3V0QWN0aW9uKCk7IGJyZWFrOwogICAgICBjYXNlICJiYWNrVG9Eb25vckhvbWUiOiBiYWNrVG9Eb25vckhvbWUoKTsgYnJlYWs7CiAgICAgIGNhc2UgImdvQm9va0FwcG9pbnRtZW50IjogZ29Cb29rQXBwb2ludG1lbnQoKTsgYnJlYWs7CiAgICAgIGNhc2UgImxvYWRTbG90cyI6IGF3YWl0IGxvYWRTbG90cygpOyBicmVhazsKICAgICAgY2FzZSAicGlja1Nsb3QiOiBwaWNrU2xvdChkYXRhLnRpbWUpOyBicmVhazsKICAgICAgY2FzZSAic3VibWl0Qm9va2luZyI6IGF3YWl0IHN1Ym1pdEJvb2tpbmcoKTsgYnJlYWs7CiAgICAgIGNhc2UgImNhbmNlbEFwcG9pbnRtZW50IjogYXdhaXQgY2FuY2VsQXBwb2ludG1lbnQoTnVtYmVyKGRhdGEuaWQpKTsgYnJlYWs7CiAgICAgIGNhc2UgImFjY2VwdFJlc2NoZWR1bGUiOiBhd2FpdCBhY2NlcHRSZXNjaGVkdWxlKE51bWJlcihkYXRhLmlkKSk7IGJyZWFrOwogICAgICBjYXNlICJvcGVuRm9sbG93VXAiOiBvcGVuRm9sbG93VXAoTnVtYmVyKGRhdGEuYXBwdCksIE51bWJlcihkYXRhLmRheSkpOyBicmVhazsKICAgICAgY2FzZSAic3VibWl0Rm9sbG93VXAiOiBhd2FpdCBzdWJtaXRGb2xsb3dVcCgpOyBicmVhazsKICAgICAgY2FzZSAidG9nZ2xlQ2FsbGJhY2siOiBzdGF0ZS5mb3JtLmNhbGxiYWNrUmVxdWVzdGVkID0gIXN0YXRlLmZvcm0uY2FsbGJhY2tSZXF1ZXN0ZWQ7IHJlbmRlcigpOyBicmVhazsKICAgICAgY2FzZSAic2V0Rm9ybSI6IGFjdGlvblNldEZvcm0oZGF0YS5rZXksIGRhdGEudmFsdWUpOyBicmVhazsKCiAgICAgIGNhc2UgInN0YWZmTG9naW5TdWJtaXQiOiBhd2FpdCBzdGFmZkxvZ2luU3VibWl0KCk7IGJyZWFrOwogICAgICBjYXNlICJzdGFmZkxvZ291dCI6IGF3YWl0IHN0YWZmTG9nb3V0QWN0aW9uKCk7IGJyZWFrOwogICAgICBjYXNlICJnb0NoYW5nZVBhc3N3b3JkIjogc3RhdGUuZm9yY2VkUHdDaGFuZ2UgPSBmYWxzZTsgc2V0U2NyZWVuKCJjaGFuZ2VQYXNzd29yZCIpOyBicmVhazsKICAgICAgY2FzZSAic3VibWl0Q2hhbmdlUGFzc3dvcmQiOiBhd2FpdCBzdWJtaXRDaGFuZ2VQYXNzd29yZCgpOyBicmVhazsKICAgICAgY2FzZSAiZ29TdGFmZkRhc2hib2FyZCI6IGF3YWl0IGdvU3RhZmZEYXNoYm9hcmRBY3Rpb24oKTsgYnJlYWs7CiAgICAgIGNhc2UgImdvTm90aWZDZW50ZXIiOiBhd2FpdCBnb05vdGlmQ2VudGVyKCk7IGJyZWFrOwogICAgICBjYXNlICJnb0Rvbm9yTGlzdCI6IGF3YWl0IGdvRG9ub3JMaXN0KCk7IGJyZWFrOwogICAgICBjYXNlICJzZWFyY2hEb25vcnMiOiBhd2FpdCBzZWFyY2hEb25vcnMoKTsgYnJlYWs7CiAgICAgIGNhc2UgImV4cG9ydENzdiI6IGV4cG9ydENzdigpOyBicmVhazsKICAgICAgY2FzZSAib3BlbkRvbm9yQnlQaG9uZSI6IGF3YWl0IG9wZW5Eb25vckJ5UGhvbmUoZGF0YS5waG9uZSk7IGJyZWFrOwogICAgICBjYXNlICJhcHByb3ZlTGFiIjogYXdhaXQgYXBwcm92ZUxhYigpOyBicmVhazsKICAgICAgY2FzZSAiYmxvY2tEb25vciI6IGF3YWl0IGJsb2NrRG9ub3IoKTsgYnJlYWs7CiAgICAgIGNhc2UgImFkZE5vdGUiOiBhd2FpdCBhZGROb3RlKCk7IGJyZWFrOwogICAgICBjYXNlICJkZWxldGVOb3RlIjogYXdhaXQgZGVsZXRlTm90ZShOdW1iZXIoZGF0YS5pZCkpOyBicmVhazsKICAgICAgY2FzZSAiYWRkUmVtaW5kZXIiOiBhd2FpdCBhZGRSZW1pbmRlcigpOyBicmVhazsKICAgICAgY2FzZSAibWFya1JlbWluZGVyRG9uZSI6IGF3YWl0IG1hcmtSZW1pbmRlckRvbmUoTnVtYmVyKGRhdGEuaWQpKTsgYnJlYWs7CiAgICAgIGNhc2UgImNvbmZpcm1BcHBvaW50bWVudCI6IGF3YWl0IGNvbmZpcm1BcHBvaW50bWVudChOdW1iZXIoZGF0YS5pZCkpOyBicmVhazsKICAgICAgY2FzZSAicHJvcG9zZVJlc2NoZWR1bGUiOiBhd2FpdCBwcm9wb3NlUmVzY2hlZHVsZShOdW1iZXIoZGF0YS5pZCkpOyBicmVhazsKICAgICAgY2FzZSAiY2FuY2VsQXBwdEFkbWluIjogYXdhaXQgY2FuY2VsQXBwdEFkbWluKE51bWJlcihkYXRhLmlkKSk7IGJyZWFrOwogICAgICBjYXNlICJvcGVuT3V0Y29tZUZvcm0iOiBvcGVuT3V0Y29tZUZvcm0oTnVtYmVyKGRhdGEuaWQpKTsgYnJlYWs7CiAgICAgIGNhc2UgInRvZ2dsZU91dGNvbWVBdHRlbmRlZCI6IHRvZ2dsZU91dGNvbWVBdHRlbmRlZCgpOyBicmVhazsKICAgICAgY2FzZSAic3VibWl0T3V0Y29tZSI6IGF3YWl0IHN1Ym1pdE91dGNvbWUoKTsgYnJlYWs7CiAgICAgIGNhc2UgImNyZWF0ZUFwcHRGb3JEb25vciI6IGF3YWl0IGNyZWF0ZUFwcHRGb3JEb25vcigpOyBicmVhazsKICAgICAgY2FzZSAiYmFja1RvRG9ub3JEZXRhaWwiOiBiYWNrVG9Eb25vckRldGFpbCgpOyBicmVhazsKICAgICAgY2FzZSAiZ29BcHBvaW50bWVudHMiOiBhd2FpdCBnb0FwcG9pbnRtZW50cygpOyBicmVhazsKICAgICAgY2FzZSAibG9hZEFkbWluU2xvdHMiOiBhd2FpdCBsb2FkQWRtaW5TbG90cygpOyBicmVhazsKICAgICAgY2FzZSAiZ29TZXR0aW5ncyI6IGF3YWl0IGdvU2V0dGluZ3MoKTsgYnJlYWs7CiAgICAgIGNhc2UgInRvZ2dsZUNsb3NlZERheSI6IHRvZ2dsZUNsb3NlZERheShOdW1iZXIoZGF0YS5kYXkpKTsgYnJlYWs7CiAgICAgIGNhc2UgInNldEFwcG9pbnRtZW50TW9kZSI6IHNldEFwcG9pbnRtZW50TW9kZShkYXRhLm1vZGUpOyBicmVhazsKICAgICAgY2FzZSAic2F2ZVNldHRpbmdzIjogYXdhaXQgc2F2ZVNldHRpbmdzKCk7IGJyZWFrOwogICAgICBjYXNlICJzYXZlU21zVGVtcGxhdGVzIjogYXdhaXQgc2F2ZVNtc1RlbXBsYXRlcygpOyBicmVhazsKICAgICAgY2FzZSAiZ29TdGFmZlVzZXJzIjogYXdhaXQgZ29TdGFmZlVzZXJzKCk7IGJyZWFrOwogICAgICBjYXNlICJhZGRTdGFmZlVzZXIiOiBhd2FpdCBhZGRTdGFmZlVzZXIoKTsgYnJlYWs7CiAgICAgIGNhc2UgInRvZ2dsZUJsb2NrU3RhZmYiOiBhd2FpdCB0b2dnbGVCbG9ja1N0YWZmKE51bWJlcihkYXRhLmlkKSwgZGF0YS5ibG9ja2VkID09PSAidHJ1ZSIpOyBicmVhazsKICAgICAgY2FzZSAiZGVsZXRlU3RhZmZVc2VyIjogYXdhaXQgZGVsZXRlU3RhZmZVc2VyKE51bWJlcihkYXRhLmlkKSk7IGJyZWFrOwogICAgICBjYXNlICJnb1ByRGFzaGJvYXJkIjogYXdhaXQgZ29QckRhc2hib2FyZCgpOyBicmVhazsKICAgICAgY2FzZSAiZ29Dcm1EYXNoYm9hcmQiOiBhd2FpdCBnb0NybURhc2hib2FyZCgpOyBicmVhazsKICAgICAgY2FzZSAiZ29BY3Rpdml0eUxvZyI6IGF3YWl0IGdvQWN0aXZpdHlMb2coKTsgYnJlYWs7CiAgICAgIGNhc2UgInByaW50UmVwb3J0IjogcHJpbnRSZXBvcnQoKTsgYnJlYWs7CiAgICAgIGNhc2UgImNoYW5nZVN0YXR1cyI6IGJyZWFrOyAvLyDYr9ixINix2YjbjNiv2KfYryBjaGFuZ2Ug2YXYr9uM2LHbjNiqINmF24zigIzYtNmHCiAgICB9CiAgfSBjYXRjaCAoZXJyKSB7IHN0YXRlLmVycm9yTXNnID0gZXJyLm1lc3NhZ2U7IHJlbmRlcigpOyB9Cn0pOwoKZG9jdW1lbnQuYWRkRXZlbnRMaXN0ZW5lcigiY2hhbmdlIiwgYXN5bmMgKGUpID0+IHsKICBpZiAoZS50YXJnZXQuZGF0YXNldCAmJiBlLnRhcmdldC5kYXRhc2V0LmFjdGlvbiA9PT0gImNoYW5nZVN0YXR1cyIpIHsKICAgIGF3YWl0IGNoYW5nZVN0YXR1c0FjdGlvbihlLnRhcmdldC52YWx1ZSk7CiAgfQp9KTsKCi8qID09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PQogICDYsdin2YfigIzYp9mG2K/Yp9iy24wg2KfZiNmE24zZhwogICA9PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT0gKi8KKGFzeW5jIGZ1bmN0aW9uIGluaXQoKSB7CiAgdHJ5IHsgc3RhdGUuc3RhZmYgPSBhd2FpdCBhcGkoIkdFVCIsICIvYXBpL3N0YWZmLWF1dGgvbWUiKTsgfSBjYXRjaCAoZSkgeyBzdGF0ZS5zdGFmZiA9IG51bGw7IH0KICByZW5kZXIoKTsKfSkoKTsK", "base64").toString("utf8");
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

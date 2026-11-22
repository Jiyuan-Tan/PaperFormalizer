import { describe, expect, it } from "vitest";
import { deriveVerifyQid, VERIFY_SLUG_MAX } from "../../src/verify/cli.js";
// @ts-expect-error a plain .mjs module of the batch driver
import { runSlug, RUN_SLUG_MAX } from "../../scripts/run_slug.mjs";

describe("the batch driver's run slug", () => {
  it("is the slug `verify --slug` creates the run under", () => {
    expect(RUN_SLUG_MAX).toBe(VERIFY_SLUG_MAX);
    for (const s of ["aaaaaaaaaaaaaaaaaaaa_bbbbbbbbbbbbbbbbbbbb", "cccccccccc_ddddddddddddddd_eeeeeeeeeeeeeee", "Ab-C.d__e", "ab_short", "x".repeat(39) + "_y", "a_b_c_d_e_f_g_h_i_j_k_l_m_n_o_p_q_r_s_t_u_v"]) {
      expect(runSlug(s)).toBe(deriveVerifyQid("ignored.tex", s));
    }
    expect(runSlug("aaaaaaaaaaaaaaaaaaaa_bbbbbbbbbbbbbbbbbbbb")).toBe("aaaaaaaaaaaaaaaaaaaa_bbbbbbbbbbbbbbbbbbb");
  });
});

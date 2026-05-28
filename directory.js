(function () {
  const script = document.currentScript;
  const root = script?.dataset.root || ".";

  document.write(`
    <div class="header">
      <table class="heading"; style="background-color: transparent; border-color: transparent;">
        <tr><td class="heading">
          <h1>Matthew Faust</h1>
          <h2>Michigan State University</h2>
          <h2>mfaust@msu.edu</h2>
        </td>
        <td class="directory">
          <table class="direct">
            <tr class="direct"><th class="direct">Directory</th></tr>
            <tr>
              <td class="direct" style="background-color:rgba(180, 228, 238, 0.932);">
                <a href="${root}/index.html">Home</a>
              </td>
            </tr>
            <tr>
              <td class="direct" style="background-color:blueviolet;">
                <a href="${root}/research/index.html">Research</a>
              </td>
            </tr>
            <tr>
              <td class="direct" style="background-color:rgb(60, 133, 0);">
                <a href="${root}/teaching/index.html">Teaching</a>
              </td>
            </tr>
            <tr>
              <td class="direct" style="background-color:rgb(168, 202, 88);">
                <a href="${root}/cv/index.html">CV</a>
              </td>
            </tr>
          </table>
        </td></tr>
      </table>
    </div>
  `);
})();

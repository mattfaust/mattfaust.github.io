(function () {
  var owner = "mattfaust";
  var repo = "mattfaust.github.io";
  var target = document.querySelector("[data-last-modified]");

  if (!target) {
    return;
  }

  function pagePath() {
    var path = window.location.pathname.replace(/^\/+/, "");

    if (path === "") {
      return "index.html";
    }

    if (path.slice(-1) === "/") {
      return path + "index.html";
    }

    return path;
  }

  function showDate(dateString) {
    var date = new Date(dateString);
    target.textContent = "Last Modified: " + date.toLocaleDateString(undefined, {
      year: "numeric",
      month: "long",
      day: "numeric"
    });
  }

  function fallback() {
    if (document.lastModified) {
      showDate(document.lastModified);
    } else {
      target.textContent = "";
    }
  }

  if (!/^https?:$/.test(window.location.protocol)) {
    fallback();
    return;
  }

  fetch("https://api.github.com/repos/" + owner + "/" + repo + "/commits?path=" + encodeURIComponent(pagePath()) + "&per_page=1")
    .then(function (response) {
      if (!response.ok) {
        throw new Error("Unable to load commit date");
      }
      return response.json();
    })
    .then(function (commits) {
      if (commits && commits.length && commits[0].commit && commits[0].commit.committer) {
        showDate(commits[0].commit.committer.date);
      } else {
        fallback();
      }
    })
    .catch(fallback);
}());

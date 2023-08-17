---
layout: page
permalink: /teaching/
title: Teaching
nav: true
nav_order: 5
---

 <article>
    <div class="cv">
      {% assign entry = site.data.teaching %}
        <a class="anchor" id="{{ entry.title }}"></a>
        <div class="card mt-3 p-3">
          <h3 class="card-title font-weight-medium">{{ entry.title }}</h3>
          <div>
	      {% include cv/time_table.html %}
          </div>
        </div>
  </div>
</article>
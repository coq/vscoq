/*
 * jQuery tbletree Plugin 1.0.0
  * 
 * Copyright 2014, Gagik Sukiasyan
 * Licensed under the MIT licenses.
 */
(function($) {
	 $.widget( "ui.tbltree", {
      // default options
      options: {
        
		rowAttr: 'row-id',
		parentAttr: 'parent-id',
		treeColumn: 0,
		
		saveState: false,
		saveStateName: 'tbltree-state',
		saveStateMethod: 'cookie',
		initState: 'collapsed',
		levelPicker: '',
		
		expanderTemplate: '<span class="tbltree-expander"></span>',
		levelPickerTemplate: '<div class="tbltree-level-pickers">\
								<span id="0" class="tbltree-level-item">[1]</span>&nbsp;\
								<span id="1" class="tbltree-level-item">[2]</span>&nbsp;\
								<span id="2" class="tbltree-level-item">[3]</span>&nbsp;\
								<span id="3" class="tbltree-level-item">[4]</span>&nbsp;\
							  </div>',
        indentTemplate: '<span class="tbltree-indent"></span>',
        expanderExpandedClass: 'tbltree-expander-expanded',
        expanderCollapsedClass: 'tbltree-expander-collapsed',
	
		
		count: {
			enabled: false,
			format: '<div class="tbltree-count-wrap">(<span class="tbltree-count"></span>)</div>',
			method: function(row) {
				// count every row
				return 1;
			},
			click: null
		},
		
        // callbacks
        change: null,
		expand: null,
		collapse: null,
		showlevel: null
      },
 
		 // the constructor
		_create: function() {
			var $this = this;
			this.element
			  .addClass( "jquery-tbltree" )
			  
			if (this.options.levelPicker !== "" && $(this.options.levelPicker).length > 0) {
				this.pickers = $(this.options.levelPickerTemplate);
				this.pickers.find('.tbltree-level-item').click(function(){
					$this.showLevel($(this).attr('id'))
				})
				$(this.options.levelPicker).append(this.pickers);
			}
		},
		_init: function() {
			var $this = this;
			this.getRootNodes().each(function(){
				$this._initTree($(this));
			})
		},
	 
		getID: function(row) {
			return row.attr(this.options.rowAttr);
		},
		getParentID: function(row) {
			return row.attr(this.options.parentAttr);
		},
		isExpanded: function(cell) {
            return cell.hasClass('tbltree-expanded');
        },
		isCollapsed: function(cell) {
            return cell.hasClass('tbltree-collapsed');
        },
		getRootNodes: function () {
			var nodes = this.element.find('tr['+this.options.rowAttr+']').not('tr['+this.options.parentAttr+']')
			return nodes
		},
		getRow: function(id) {
			return this.element.find('tr['+this.options.rowAttr+'="'+id+'"]');
		},
		
		saveState: function(row) {
            var $this = this;
            if ($this.options.saveState && $this.options.saveStateMethod === 'cookie') {

                var stateArrayString = $.cookie(this.options.saveStateName) || '';
                var stateArray = (stateArrayString === '' ? [] : stateArrayString.split(','));
                var nodeId = $this.getID(row);

                if ($this.isExpanded(row)) {
                    if ($.inArray(nodeId, stateArray) === -1) {
                        stateArray.push(nodeId);
                    }
                } else if ($this.isCollapsed(row)) {
                    if ($.inArray(nodeId, stateArray) !== -1) {
                        stateArray.splice($.inArray(nodeId, stateArray), 1);
                    }
                }
                $.cookie(this.options.saveStateName, stateArray.join(','));
            }
            return $this;
        },
		getState: function(row) {
            var $this = this;
			
            if ($this.options.saveState && $this.options.saveStateMethod === 'cookie') {
				var stateArrayString = $.cookie(this.options.saveStateName) || '';
                var stateArray = (stateArrayString === '' ? [] : stateArrayString.split(','));
                if ($.inArray($this.getID(row), stateArray) !== -1) {
                    return "expanded";
                } else {
					return "collapsed";
                }

            }
            return $this.options.initState;
        },
		
		toggle: function (row) {
			if (typeof(row) != "object") {
				row = this.getRow(row);
			} 
			if (this.isCollapsed(row)) {
				this.expand(row, 1);
				
			} else {
				this.collapse(row, 1);
			}
		},
		
		collapse: function(id, user) {
				var $this = this;
				
				if (typeof(id) === "object") {
					row_id = this.getID(id);
					row = id;
				} else {
					row_id = id;
					row = this.getRow(row_id);
				}
				
				
				var row_id = this.getID(row);	
				if (user) {
					this.render(row, 'collapsed');
					this.saveState(row);
					this._trigger("collapse", null, row);
					this._trigger("change", null, {type: 'collapsed', 'row': row});
				}
				
				this._getChildren(row_id).each(function(){
					$(this).hide();
					$this.collapse($(this), 0);
				})
		},
		expand: function(id, user) {
				var $this = this;
				
				if (typeof(id) === "object") {
					row_id = this.getID(id);
					row = id;
				} else {
					row_id = id;
					row = this.getRow(row_id);
				}
				
				var row_id = this.getID(row);	
				if (user) {
					this.render(row, 'expanded')
					this.saveState(row);
					this._trigger("expand", null, row);
					this._trigger("change", null, {type: 'expanded', 'row': row});
				} 
				
				this._getChildren(row_id).each(function(){
					if ( ! $this.isCollapsed($(this))) {
						$this.expand($(this), 0);
					}
					$(this).show();
				})
		},
		
		expandLevel: function(level) {
			var $this = this;
			$this.element.find('tr[level]').filter(function() {
			    return  $(this).attr("level") <= level;
			})
			.each(function(){
				$this.expand($(this), 1);
			})
		},
		
		collapseLevel: function(level) {
			var $this = this;
			$this.element.find('tr[level='+level+']').each(function(){
					$this.collapse($(this), 1);
			})
			
		},
		
		showLevel: function(level) {
			var $this = this;
			if (level > 0) {
				$this.expandLevel(level - 1);
			}
			$this.collapseLevel(level);
			this._trigger("showlevel", null, level);
		},
		
		render: function(row, state) {
			var $this = this;
			if (state == 'collapsed') {
				row.attr('tree-state', 'hidden')
				row.removeClass('tbltree-expanded');
				row.addClass('tbltree-collapsed');
			} else {
				row.attr('tree-state', 'shown')
				row.removeClass('tbltree-collapsed');
				row.addClass('tbltree-expanded');
			}
			this._renderExpander(row);
        },
		
		_getChildren: function (id) {
			if (typeof(id) === "object") {
				id = this.getID(id);	
			}
			return this.element.find('tr['+this.options.parentAttr+'="'+id+'"]');
		},
		
		getTreeCell: function (row) {
			return $(row.find('td').get(this.options.treeColumn));
		},
		
		isLeaf: function(row) {
			if (row.attr('is-leaf') == "true") {
				return true;
			}
			return false;
		},
		
		_initExpander: function(root) {
            var $this = this;
			
           var cell = this.getTreeCell(root);
		  
            var tpl = $(this.options.expanderTemplate);
            var expander = root.find('.tbltree-expander');
            if (expander) {
                expander.remove();
            }
			tpl.prependTo(cell)
			
			tpl.click(function() {
				$this.toggle(root)
            });
			
        },
		_renderExpander: function(cell) {
			if (cell.attr('is-leaf') == "true") {
				return;
			}
			var expander = cell.find('.tbltree-expander');
			if (expander.length) {
                if (!this.isCollapsed(cell)) {
                    expander.removeClass(this.options.expanderCollapsedClass);
                    expander.addClass(this.options.expanderExpandedClass);
                } else {
					expander.removeClass(this.options.expanderExpandedClass);
                    expander.addClass(this.options.expanderCollapsedClass);
                }
			} else {
                this._initExpander(cell);
				this._renderExpander(cell);
            }
        },
		
        _initIndent: function(cell, level) {
            cell.find('.tbltree-indent').remove();			
			var $indent = $(this.options.indentTemplate);
			$indent.css('width', (level * 16));
			$indent.insertBefore(cell.find('.tbltree-expander'));
        },
		
		_initTree: function(row, parent, level) {
			var $this = this;
			level = (level == undefined) ? 0: level;
			
			var children = this._getChildren(row);
			
			$this._initExpander(row);
			$this._initIndent(row, level)
			row.attr('level', level);
			row.attr('is-leaf', (children.length == 0));
			
			$this.render(row, this.getState(row));
			
			if (parent !== undefined && parent.attr('tree-state') == 'hidden') {
				row.hide();
				row.attr('tree-state', 'hidden');
			} else {
				row.show();
			}
			if (children.length != 0) {
				var count = $this._getCount(row);
				$.each(children, function(i, tree){
					$this._initTree($(tree), row, level+1);
					count += $this._getCount($(tree));
				})
				
				$this._setCount(row, count);
			} 
		},
		
		_getCount: function(row) {
			if (!this.options.count.enabled) {
				return 0;
			}
		
			var count = row.attr('count');
			if (count != undefined) {
				return parseInt(count);
			}
			count = 0;
			if (typeof(this.options.count.method) === "function") {
				count += parseInt(this.options.count.method(row));
			}
			return count;
		},
		
		_setCount: function(row, count) {		
			if (!this.options.count.enabled) {
				return 0;
			}
			
			var $this = this;
			if (typeof(this.options.count.format) === "function") {
				this.options.count.format(row, count);
			} else {
				var elem = $(this.options.count.format);
				elem.find('.tbltree-count').text(count)
				elem.appendTo(this.getTreeCell(row))
				
				if (typeof(this.options.count.click) === "function") {
					elem.css('cursor', 'pointer').click(function(e) {
						$this.options.count.click(e, row, count)
					} )
				}
			}
			row.attr('count', count);
		},
	   
      // events bound via _on are removed automatically
      // revert other modifications here
      _destroy: function() {
        this.element
          .removeClass( "jquery-tbltree" )
          .enableSelection()
        
		this.pickers.remove();  
      },
 
      // _setOptions is called with a hash of all options that are changing
      // always refresh when changing options
      _setOptions: function() {
        // _super and _superApply handle keeping the right this-context
        this._superApply( arguments );
      },
 
      // _setOption is called for each individual option that is changing
      _setOption: function( key, value ) {
        // prevent invalid color values
        this._super( key, value );
      }
    });
   
})(jQuery);
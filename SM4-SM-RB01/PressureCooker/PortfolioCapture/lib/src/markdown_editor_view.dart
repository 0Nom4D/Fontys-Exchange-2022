import 'package:flutter/material.dart';
import 'package:flutter_expandable_fab/flutter_expandable_fab.dart';

import 'package:flutter_markdown/flutter_markdown.dart';
import 'package:image_picker/image_picker.dart';
import 'package:markdown/markdown.dart' as md;
import 'package:provider/provider.dart';

import '../providers/portfolio_provider.dart';

class MarkdownEditorView extends StatefulWidget {
  final int currentEditedPortfolio;
  final int currentEditedSection;

  const MarkdownEditorView(this.currentEditedPortfolio, this.currentEditedSection, {super.key});

  @override
  State<StatefulWidget> createState() => MarkdownEditorViewState();
}

class MarkdownEditorViewState extends State<MarkdownEditorView> {
  final _key = GlobalKey<ExpandableFabState>();

  final TextEditingController _controller = TextEditingController();
  final ScrollController _mainScrollCtrlr = ScrollController();
  final ScrollController _scrollController = ScrollController();

  final String markdownHelpSheet = """Here is some little tips for Markdown writing:
    # text makes text a title. The more '#' you add, the tinier your title will be.
    *text* makes text italic.
    **text** makes text bold.
    ***text*** makes text bold and italic.
    - text makes text a point in a list.
""";

  final ImagePicker _picker = ImagePicker();

  late String? _codeExt;

  final Map<String, String> correspondingExtensions = {
    "Javascript": 'js',
    "Typescript": 'ts',
    "Dart / Flutter": 'dart',
    "Java": 'java',
    "Kotlin": 'kotlin',
  };

  @override
  void initState() {
    super.initState();

    PortfolioProvider prov = Provider.of<PortfolioProvider>(context, listen: false);
    _controller.text = prov.getPortfolioAtIndex(widget.currentEditedPortfolio).sections[widget.currentEditedSection].content;
    _codeExt = "Javascript";
  }

  addToMarkdownText(PortfolioProvider prov, String value) {
    prov.addToPortfolioSection(widget.currentEditedPortfolio, widget.currentEditedSection, value);
    _controller.text += value;
  }

  // Functions to create BottomSheet with DropdownButton
  createBox(BuildContext context, StateSetter state) {
    return SingleChildScrollView(
      child: LimitedBox(
        //maxHeight: MediaQuery.of(context).size.height / 1.5,
        child: Column(
          mainAxisSize: MainAxisSize.max,
          mainAxisAlignment: MainAxisAlignment.center,
          children: <Widget>[
            const Padding(
              padding: EdgeInsets.symmetric(vertical: 10),
              child: Text('Embded Code Markdown Implementation')
            ),
            buildMainDropdown(state),
            Row(
              mainAxisAlignment: MainAxisAlignment.center,
              crossAxisAlignment: CrossAxisAlignment.center,
              children: <Widget>[
                Expanded(
                  child: Padding(
                    padding: EdgeInsets.symmetric(horizontal: MediaQuery.of(context).size.width * .02),
                    child: ElevatedButton(
                      onPressed: () {
                        Navigator.pop(context, null);
                      },
                      child: const Text("Cancel"),
                    )
                  )
                ),
                Expanded(
                  child: Padding(
                    padding: EdgeInsets.symmetric(horizontal: MediaQuery.of(context).size.width * .02),
                    child: ElevatedButton(
                      onPressed: () {
                        Navigator.pop(context, _codeExt);
                      },
                      child: const Text("Confirm"),
                    )
                  )
                ),
              ],
            )
          ]
        )
      )
    );

  }

  DropdownButtonHideUnderline buildMainDropdown(StateSetter setState) {
    return DropdownButtonHideUnderline(
      child: DropdownButton(
        value: _codeExt,
        hint: const Text("Select a programming language"),
        items: <String>[
          "Javascript",
          "Typescript",
          "Dart / Flutter",
          "Java",
          "Kotlin"
        ].map<DropdownMenuItem<String>>((String item) =>
            DropdownMenuItem<String>(value: item, child: Text(item)))
        .toList(),
        onChanged: (newExt) {
          setState(() {
            _codeExt = newExt;
          });
        },
      ),
    );
  }

  @override
  Widget build(BuildContext context) {
    PortfolioProvider prov = Provider.of<PortfolioProvider>(context);

    return Scaffold(
      appBar: AppBar(title: const Text("ProdigyPort")),
      resizeToAvoidBottomInset: true,
      floatingActionButtonLocation: ExpandableFab.location,
      floatingActionButton: ExpandableFab(
        child: const Icon(Icons.add),
        key: _key,
        children: [
          FloatingActionButton.small(
            heroTag: null,
            tooltip: "Add a link to an online video",
            onPressed: () async {
              String? dialogResponse = await showDialog<String?>(
                context: context,
                barrierDismissible: false,
                builder: (BuildContext context) {
                  TextEditingController textController = TextEditingController();
                  TextEditingController linkController = TextEditingController();
                  String textLink = "";
                  String videoLink = "";

                  return AlertDialog(
                    title: const Text("Video Link Implementation"),
                    content: Padding(
                      padding: const EdgeInsets.symmetric(vertical: 10),
                      child: Column(
                        mainAxisSize: MainAxisSize.min,
                        children: <Widget>[
                          TextField(
                            controller: textController,
                            onChanged: (value) {
                              textLink = value;
                            },
                            decoration: const InputDecoration(
                              border: OutlineInputBorder(),
                              hintText: "Text you will click on to access the video",
                            ),
                          ),
                          const SizedBox(height: 10),
                          TextField(
                            controller: linkController,
                            onChanged: (value) {
                              videoLink = value;
                            },
                            decoration: const InputDecoration(
                              border: OutlineInputBorder(),
                              hintText: "Link to your video",
                            ),
                          )
                        ],
                      )
                    ),
                    actions: <Widget>[
                      TextButton(
                        onPressed: () => Navigator.pop(context, null),
                        child: const Text('Cancel'),
                      ),
                      TextButton(
                        onPressed: () {
                          Navigator.pop(context, "[$textLink]($videoLink)");
                        },
                        child: const Text('OK'),
                      ),
                    ],
                  );
                }
              );
              if (dialogResponse == null) {
                return;
              }
              addToMarkdownText(prov, dialogResponse);
            },
            child: const Icon(Icons.video_camera_front)
          ),
          FloatingActionButton.small(
            heroTag: null,
            tooltip: "Add images from gallery",
            onPressed: () async {
              List<XFile>? images = await _picker.pickMultiImage();

              if (images.isEmpty) {
                return;
              }
              String imageWrapper = "";
              for (XFile image in images) {
                imageWrapper += "\n![AltText](${image.path})";
              }
              addToMarkdownText(prov, imageWrapper);
            },
            child: const Icon(Icons.browse_gallery)
          ),
          FloatingActionButton.small(
            heroTag: null,
            tooltip: "Add a photo from camera",
            onPressed: () async {
              XFile? image = await _picker.pickImage(source: ImageSource.camera);

              if (image == null) {
                return;
              }
              addToMarkdownText(prov, "\n![AltText](${image.path})");
            },
            child: const Icon(Icons.add_a_photo)
          ),
          FloatingActionButton.small(
            heroTag: null,
            tooltip: "Add a code snippet",
            onPressed: () async {
              String? chosenCodeExt = await showModalBottomSheet<String?>(
                context: context,
                builder: (BuildContext context) {
                  return StatefulBuilder(
                    builder: (BuildContext context, StateSetter state) {
                      return createBox(context, state);
                    }
                  );
                }
              );

              if (chosenCodeExt == null) {
                return;
              }
              addToMarkdownText(prov, """

```${correspondingExtensions[_codeExt]}
Write your $_codeExt code here
```
"""
              );
            },
            child: const Icon(Icons.code)
          ),
        ],
      ),
      body: Consumer<PortfolioProvider>(
        builder: (context, provider, _) =>
          SafeArea(
            child: SingleChildScrollView(
              controller: _mainScrollCtrlr,
              child: Padding(
                padding: const EdgeInsets.all(20),
                child: Column(
                  children: <Widget>[
                    TextField(
                      onChanged: (String newText) {
                        provider.updatePortfolioSection(widget.currentEditedPortfolio, widget.currentEditedSection, _controller.text);
                      },
                      controller: _controller,
                      scrollController: _scrollController,
                      keyboardType: TextInputType.multiline,
                      maxLines: null,
                      decoration: const InputDecoration(
                        border: OutlineInputBorder(),
                        hintText: "Write your portfolio here",
                      ),
                    ),
                    Padding(
                      padding: const EdgeInsets.only(top: 15, bottom: 5),
                      child: ExpansionTile(
                        leading: const Icon(Icons.help),
                        title: const Text("Need any help?"),
                        children: [
                          ListTile(
                            title: Text(markdownHelpSheet)
                          )
                        ],
                      )
                    ),
                    const Padding(
                      padding: EdgeInsets.symmetric(vertical: 10),
                      child: Divider(
                        thickness: 2.5
                      ),
                    ),
                    const Padding(
                      padding: EdgeInsets.symmetric(vertical: 15),
                      child: Align(
                        alignment: Alignment.centerLeft,
                        child: Text("Your portfolio will be displayed here:",)
                      ),
                    ),
                    MarkdownBody(
                      styleSheetTheme: MarkdownStyleSheetBaseTheme.cupertino,
                      extensionSet: md.ExtensionSet(
                        md.ExtensionSet.gitHubFlavored.blockSyntaxes,
                        [md.EmojiSyntax(), ...md.ExtensionSet.gitHubFlavored.inlineSyntaxes],
                      ),
                      data: provider.getPortfolioAtIndex(widget.currentEditedPortfolio).sections[widget.currentEditedSection].content,
                      styleSheet: MarkdownStyleSheet(
                        textAlign: WrapAlignment.start,
                      ),
                    ),
                  ],
                ),
              ),
            )
        ),
      ),
    );
  }
}
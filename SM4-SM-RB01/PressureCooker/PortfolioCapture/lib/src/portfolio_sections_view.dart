import 'package:flutter/material.dart';
import 'package:portfolio_capture/models/section_model.dart';
import 'package:provider/provider.dart';

import '../models/portfolio_model.dart';
import '../providers/portfolio_provider.dart';
import 'markdown_editor_view.dart';

class PortfolioSections extends StatefulWidget {
  final int currentModifiedPortfolio;

  const PortfolioSections(this.currentModifiedPortfolio, {super.key});

  @override
  State<StatefulWidget> createState() => PortfolioSectionsState();
}

class PortfolioSectionsState extends State<PortfolioSections> {
  @override
  void initState() {
    super.initState();
  }

  String cropContent(String content) {
    if (content.length < 50) {
      return content;
    }
    return "${content.substring(0, 50)}...";
  }

  Widget createSubsectionDialog(String newName) {
    return AlertDialog(
      title: const Text("New subsection"),
      content: TextField(
        maxLines: 1,
        onChanged: (value) => {
          newName = value
        },
        decoration: InputDecoration(
          prefixIcon: const Icon(Icons.edit),
          hintText: "New subsection title",
          border: OutlineInputBorder(
            borderRadius: BorderRadius.circular(10),
          )
        ),
      ),
      actions: <Widget>[
        TextButton(
          onPressed: () => Navigator.pop(context, null),
          child: const Text('Cancel'),
        ),
        TextButton(
          onPressed: () {
            Navigator.pop(context, newName);
          },
          child: const Text('OK'),
        ),
      ],
    );
  }

  @override
  Widget build(BuildContext context) {
    PortfolioProvider portfolioProvider = Provider.of<PortfolioProvider>(context);

    return Scaffold(
      appBar: AppBar(title: const Text("ProdigyPort")),
      resizeToAvoidBottomInset: true,
      floatingActionButton: FloatingActionButton(
        heroTag: null,
        tooltip: "Create a new subsection",
        onPressed: () async {
          PortfolioSection newSection;
          String? newSubsectionName;

          newSubsectionName = await showDialog<String?>(
            context: context,
            builder: (BuildContext context) {
              String newName = "";

              return createSubsectionDialog(newName);
            }
          );
          if (newSubsectionName == null) {
            return;
          }

          newSection = PortfolioSection(
            id: portfolioProvider.getPortfolioAtIndex(widget.currentModifiedPortfolio).sections.length.toString(),
            name: newSubsectionName,
            content: """
### $newSubsectionName

"""
          );

          portfolioProvider.addSectionToPortfolioAtIndex(widget.currentModifiedPortfolio, newSection);

          if (context.mounted) {
            Navigator.push(
              context,
              MaterialPageRoute(
                builder: (context) => MarkdownEditorView(widget.currentModifiedPortfolio, int.parse(newSection.id))
              )
            );
          }
        },
        child: const Icon(Icons.add),
      ),
      body: portfolioProvider.getPortfolioAtIndex(widget.currentModifiedPortfolio).sections.isNotEmpty ?
        Consumer<PortfolioProvider>(
          builder: (context, provider, _) {
            Portfolio currentModifiedPortfolio = provider.getPortfolioAtIndex(
                widget.currentModifiedPortfolio);

            return ListView.separated(
              padding: const EdgeInsets.all(10),
              itemBuilder: (BuildContext context, int index) {
                return GestureDetector(
                  onTap: () {
                    Navigator.push(
                      context,
                      MaterialPageRoute(
                        builder: (context) =>
                          MarkdownEditorView(widget.currentModifiedPortfolio, index)
                      )
                    );
                  },
                  child: Card(
                    elevation: 20,
                    child: Column(
                      children: <Widget>[
                        ListTile(
                          leading: const Icon(Icons.file_copy),
                          title: Text(
                            currentModifiedPortfolio.sections[index].name),
                          subtitle: Text(cropContent(
                            currentModifiedPortfolio.sections[index]
                                .content)),
                          trailing: IconButton(
                              onPressed: () {
                                provider.deleteSectionAtIndex(widget.currentModifiedPortfolio, index);
                              },
                              icon: const Icon(Icons.cancel_outlined)
                          ),
                        )
                      ],
                    )
                  ),
                );
              },
              separatorBuilder: (BuildContext context,
                  int index) => const Divider(),
              itemCount: currentModifiedPortfolio.sections.length,
            );
          }
        ) : const Center(
          child: Text("That portfolio doesn't have any subsections.")
      ),
    );
  }
}